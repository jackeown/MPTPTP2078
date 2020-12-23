%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r32X5RU97c

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 494 expanded)
%              Number of leaves         :   24 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  634 (4689 expanded)
%              Number of equality atoms :   36 ( 248 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( r2_hidden @ ( sk_C_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( r2_hidden @ ( sk_C_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t32_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ~ ( ( r1_tarski @ A @ B )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ~ ( ( r2_hidden @ C @ A )
                  & ! [D: $i] :
                      ( ( v3_ordinal1 @ D )
                     => ( ( r2_hidden @ D @ A )
                       => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v3_ordinal1 @ B )
       => ~ ( ( r1_tarski @ A @ B )
            & ( A != k1_xboole_0 )
            & ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ~ ( ( r2_hidden @ C @ A )
                    & ! [D: $i] :
                        ( ( v3_ordinal1 @ D )
                       => ( ( r2_hidden @ D @ A )
                         => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_ordinal1])).

thf('19',plain,(
    ! [X53: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X53 ) @ sk_A )
      | ~ ( r2_hidden @ X53 @ sk_A )
      | ~ ( v3_ordinal1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( r2_hidden @ ( sk_C_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('28',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('38',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v3_ordinal1 @ X49 )
      | ( r1_ordinal1 @ X50 @ X49 )
      | ( r2_hidden @ X49 @ X50 )
      | ~ ( v3_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('50',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ X44 @ X43 )
      | ~ ( r2_hidden @ X44 @ ( sk_C_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,
    ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('56',plain,(
    ! [X53: $i] :
      ( ( v3_ordinal1 @ ( sk_D_1 @ X53 ) )
      | ~ ( r2_hidden @ X53 @ sk_A )
      | ~ ( v3_ordinal1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X53: $i] :
      ( ~ ( r1_ordinal1 @ X53 @ ( sk_D_1 @ X53 ) )
      | ~ ( r2_hidden @ X53 @ sk_A )
      | ~ ( v3_ordinal1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('66',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( r2_hidden @ ( sk_C_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('68',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['64','65','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r32X5RU97c
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:41:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 349 iterations in 0.183s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.46/0.66  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.46/0.66  thf(d5_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.66       ( ![D:$i]:
% 0.46/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.66           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.46/0.66         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.46/0.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.46/0.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.66  thf(t2_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.66  thf(t100_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.66           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf(t5_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.66  thf('4', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.66  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X8 @ X7)
% 0.46/0.66          | ~ (r2_hidden @ X8 @ X6)
% 0.46/0.66          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.66          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.66  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.66      inference('condensation', [status(thm)], ['8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.66          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.46/0.66  thf(t7_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ~( ( r2_hidden @ A @ B ) & 
% 0.46/0.66          ( ![C:$i]:
% 0.46/0.66            ( ~( ( r2_hidden @ C @ B ) & 
% 0.46/0.66                 ( ![D:$i]:
% 0.46/0.66                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X42 : $i, X43 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X42 @ X43) | (r2_hidden @ (sk_C_1 @ X43) @ X43))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1))
% 0.46/0.66          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.46/0.66         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.46/0.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.46/0.66          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.46/0.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('eq_fact', [status(thm)], ['13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X42 : $i, X43 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X42 @ X43) | (r2_hidden @ (sk_C_1 @ X43) @ X43))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) = (k4_xboole_0 @ X0 @ X1)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C_1 @ X0) @ X0)
% 0.46/0.66          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['12', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]: ((r2_hidden @ (sk_C_1 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf(t32_ordinal1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v3_ordinal1 @ B ) =>
% 0.46/0.66       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66            ( ![C:$i]:
% 0.46/0.66              ( ( v3_ordinal1 @ C ) =>
% 0.46/0.66                ( ~( ( r2_hidden @ C @ A ) & 
% 0.46/0.66                     ( ![D:$i]:
% 0.46/0.66                       ( ( v3_ordinal1 @ D ) =>
% 0.46/0.66                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( v3_ordinal1 @ B ) =>
% 0.46/0.66          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66               ( ![C:$i]:
% 0.46/0.66                 ( ( v3_ordinal1 @ C ) =>
% 0.46/0.66                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.46/0.66                        ( ![D:$i]:
% 0.46/0.66                          ( ( v3_ordinal1 @ D ) =>
% 0.46/0.66                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X53 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D_1 @ X53) @ sk_A)
% 0.46/0.66          | ~ (r2_hidden @ X53 @ sk_A)
% 0.46/0.66          | ~ (v3_ordinal1 @ X53))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))
% 0.46/0.66        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.46/0.66        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.66  thf(d3_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X1 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X42 : $i, X43 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X42 @ X43) | (r2_hidden @ (sk_C_1 @ X43) @ X43))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.66          | (r2_hidden @ X0 @ X2)
% 0.46/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '26'])).
% 0.46/0.66  thf(t23_ordinal1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X47 : $i, X48 : $i]:
% 0.46/0.66         ((v3_ordinal1 @ X47)
% 0.46/0.66          | ~ (v3_ordinal1 @ X48)
% 0.46/0.66          | ~ (r2_hidden @ X47 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_tarski @ sk_A @ X0)
% 0.46/0.66          | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.66          | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.66          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.46/0.66  thf(t7_ordinal1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X51 : $i, X52 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1))
% 0.46/0.66          | ~ (r1_tarski @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.46/0.66          | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.46/0.66          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('eq_fact', [status(thm)], ['13'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X51 : $i, X52 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.46/0.66          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.46/0.66          | ((sk_A) = (k4_xboole_0 @ sk_A @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['36', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))
% 0.46/0.66        | (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.46/0.66        | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['35', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (((v3_ordinal1 @ (sk_C_1 @ sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['41'])).
% 0.46/0.66  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('44', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))
% 0.46/0.66        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '44'])).
% 0.46/0.66  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('47', plain, ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('48', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf(t26_ordinal1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.66           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X49 : $i, X50 : $i]:
% 0.46/0.66         (~ (v3_ordinal1 @ X49)
% 0.46/0.66          | (r1_ordinal1 @ X50 @ X49)
% 0.46/0.66          | (r2_hidden @ X49 @ X50)
% 0.46/0.66          | ~ (v3_ordinal1 @ X50))),
% 0.46/0.66      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X42 @ X43)
% 0.46/0.66          | ~ (r2_hidden @ X44 @ X43)
% 0.46/0.66          | ~ (r2_hidden @ X44 @ (sk_C_1 @ X43)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.66      inference('condensation', [status(thm)], ['50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.46/0.66          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.46/0.66          | ~ (v3_ordinal1 @ X1)
% 0.46/0.66          | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.66          | ~ (v3_ordinal1 @ X0)
% 0.46/0.66          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['48', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D_1 @ (sk_C_1 @ sk_A)))
% 0.46/0.66        | ~ (v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['47', '53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X0 : $i]: ((r2_hidden @ (sk_C_1 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X53 : $i]:
% 0.46/0.66         ((v3_ordinal1 @ (sk_D_1 @ X53))
% 0.46/0.66          | ~ (r2_hidden @ X53 @ sk_A)
% 0.46/0.66          | ~ (v3_ordinal1 @ X53))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))
% 0.46/0.66        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.46/0.66        | (v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0)) | (v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.66  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('61', plain, ((v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D_1 @ (sk_C_1 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['54', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X53 : $i]:
% 0.46/0.66         (~ (r1_ordinal1 @ X53 @ (sk_D_1 @ X53))
% 0.46/0.66          | ~ (r2_hidden @ X53 @ sk_A)
% 0.46/0.66          | ~ (v3_ordinal1 @ X53))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.46/0.66        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('65', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('66', plain, ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X42 : $i, X43 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X42 @ X43) | (r2_hidden @ (sk_C_1 @ X43) @ X43))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.66  thf('68', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('69', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
