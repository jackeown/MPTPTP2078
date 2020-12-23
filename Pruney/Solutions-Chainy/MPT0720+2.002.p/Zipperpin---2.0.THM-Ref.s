%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.siAKwNeHs6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:34 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 436 expanded)
%              Number of leaves         :   21 ( 137 expanded)
%              Depth                    :   26
%              Number of atoms          : 1078 (5102 expanded)
%              Number of equality atoms :   50 ( 194 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19 = k1_xboole_0 )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v5_funct_1 @ X14 @ X15 )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X16 ) @ ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v5_funct_1 @ X14 @ X15 )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X16 ) @ ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
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

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X12 @ X9 ) @ ( sk_D @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k4_tarski @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(eq_fact,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ X18 )
      | ( X20
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('69',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X20
        = ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('70',plain,(
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
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['67','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','76','77','78'])).

thf('80',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('84',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.siAKwNeHs6
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 272 iterations in 0.192s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.64  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(d4_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i,C:$i]:
% 0.46/0.64         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.64             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.46/0.64               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.64           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.46/0.64             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.46/0.64               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ((r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.46/0.64          | ((X19) = (k1_xboole_0))
% 0.46/0.64          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ~ (v1_relat_1 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X18)
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ((k1_funct_1 @ X18 @ X17) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.64  thf(d3_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(t175_funct_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v5_funct_1 @ B @ A ) ) =>
% 0.46/0.64           ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & 
% 0.46/0.64                ( v5_funct_1 @ B @ A ) ) =>
% 0.46/0.64              ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t175_funct_1])).
% 0.46/0.64  thf('4', plain, ((v5_funct_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf(d20_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64           ( ( v5_funct_1 @ B @ A ) <=>
% 0.46/0.64             ( ![C:$i]:
% 0.46/0.64               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.64                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X14)
% 0.46/0.64          | ~ (v1_funct_1 @ X14)
% 0.46/0.64          | ~ (v5_funct_1 @ X14 @ X15)
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ X14 @ X16) @ (k1_funct_1 @ X15 @ X16))
% 0.46/0.64          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 0.46/0.64          | ~ (v1_funct_1 @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.46/0.64             (k1_funct_1 @ X2 @ (sk_C @ X1 @ (k1_relat_1 @ X0))))
% 0.46/0.64          | ~ (v5_funct_1 @ X0 @ X2)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ sk_B)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))) @ 
% 0.46/0.64             (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.64          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '7'])).
% 0.46/0.64  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ 
% 0.46/0.64           (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))) @ 
% 0.46/0.64           (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (((r2_hidden @ 
% 0.46/0.64         (k1_funct_1 @ sk_B @ 
% 0.46/0.64          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) @ 
% 0.46/0.64         k1_xboole_0)
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('16', plain, ((v5_funct_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X18)
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ((k1_funct_1 @ X18 @ X17) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X14)
% 0.46/0.64          | ~ (v1_funct_1 @ X14)
% 0.46/0.64          | ~ (v5_funct_1 @ X14 @ X15)
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ X14 @ X16) @ (k1_funct_1 @ X15 @ X16))
% 0.46/0.64          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X14))
% 0.46/0.64          | ~ (v1_funct_1 @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k1_funct_1 @ X2 @ X1))
% 0.46/0.64          | ~ (v5_funct_1 @ X0 @ X2)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v5_funct_1 @ X0 @ X2)
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k1_funct_1 @ X2 @ X1))
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.64          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.64          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '20'])).
% 0.46/0.64  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ 
% 0.46/0.64           (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 0.46/0.64           k1_xboole_0)
% 0.46/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.46/0.64              = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '26'])).
% 0.46/0.64  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ 
% 0.46/0.64           (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 0.46/0.64           k1_xboole_0)
% 0.46/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.46/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.46/0.64              = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('31', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.64          | (r2_hidden @ X2 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.46/0.64            = (k1_xboole_0))
% 0.46/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.64  thf(d4_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.64           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X9 : $i, X12 : $i]:
% 0.46/0.64         (((X12) = (k1_relat_1 @ X9))
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k4_tarski @ (sk_C_1 @ X12 @ X9) @ (sk_D @ X12 @ X9)) @ X9)
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.46/0.64              (sk_D @ X0 @ k1_xboole_0)) @ 
% 0.46/0.64             X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.46/0.64              (sk_D @ X0 @ k1_xboole_0)) @ 
% 0.46/0.64             X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf(antisymmetry_r2_hidden, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X1 @ k1_xboole_0) @ X1)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ 
% 0.46/0.64               (k4_tarski @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.46/0.64                (sk_D @ X1 @ k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X1 @ k1_xboole_0) @ X1)
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.46/0.64      inference('eq_fact', [status(thm)], ['41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.64          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.46/0.64        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['48', '51'])).
% 0.46/0.64  thf('53', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.46/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.46/0.64              = (k1_xboole_0))
% 0.46/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.46/0.64              = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '54'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.46/0.64            = (k1_xboole_0))
% 0.46/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X17 @ X20) @ X18)
% 0.46/0.64          | ((X20) != (k1_funct_1 @ X18 @ X17))
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ~ (v1_relat_1 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X18)
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.46/0.64          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.46/0.64              (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0)))) @ 
% 0.46/0.64             X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['57', '59'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (((r2_hidden @ 
% 0.46/0.64         (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.46/0.64          k1_xboole_0) @ 
% 0.46/0.64         sk_B)
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['56', '60'])).
% 0.46/0.64  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (((r2_hidden @ 
% 0.46/0.64         (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.46/0.64          k1_xboole_0) @ 
% 0.46/0.64         sk_B)
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.46/0.64        | (r2_hidden @ 
% 0.46/0.64           (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.46/0.64            k1_xboole_0) @ 
% 0.46/0.64           sk_B))),
% 0.46/0.64      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.64  thf('66', plain, (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      ((r2_hidden @ 
% 0.46/0.64        (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.46/0.64         k1_xboole_0) @ 
% 0.46/0.64        sk_B)),
% 0.46/0.64      inference('clc', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X18)
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ((k1_funct_1 @ X18 @ X17) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.46/0.64          | ((X20) = (k1_funct_1 @ X18 @ X17))
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X17 @ X20) @ X18)
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ~ (v1_relat_1 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.46/0.64          | ((X2) = (k1_funct_1 @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((X2) = (k1_funct_1 @ X0 @ X1))
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      ((((k1_funct_1 @ sk_B @ 
% 0.46/0.64          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) = (k1_xboole_0))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.64        | ((k1_xboole_0)
% 0.46/0.64            = (k1_funct_1 @ sk_B @ 
% 0.46/0.64               (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['67', '71'])).
% 0.46/0.64  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      ((((k1_funct_1 @ sk_B @ 
% 0.46/0.64          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) = (k1_xboole_0))
% 0.46/0.64        | ((k1_xboole_0)
% 0.46/0.64            = (k1_funct_1 @ sk_B @ 
% 0.46/0.64               (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.46/0.64         = (k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.64  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('78', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.46/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['14', '76', '77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.46/0.64        | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['79'])).
% 0.46/0.64  thf('81', plain, (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('clc', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.46/0.64  thf('84', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.64  thf('85', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('clc', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('86', plain, ($false), inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
