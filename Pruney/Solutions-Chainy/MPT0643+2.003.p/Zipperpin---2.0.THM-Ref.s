%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0HMo6wjZC4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:13 EST 2020

% Result     : Theorem 24.32s
% Output     : Refutation 24.32s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 567 expanded)
%              Number of leaves         :   25 ( 169 expanded)
%              Depth                    :   22
%              Number of atoms          : 1400 (10240 expanded)
%              Number of equality atoms :  108 (1145 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t50_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = A )
                & ( ( k1_relat_1 @ C )
                  = A )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( v2_funct_1 @ B )
                & ( ( k5_relat_1 @ C @ B )
                  = B ) )
             => ( C
                = ( k6_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != X24 )
      | ( r2_hidden @ ( sk_C_4 @ X25 @ X24 ) @ X24 )
      | ( X25
        = ( k6_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X25
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ X25 @ ( k1_relat_1 @ X25 ) ) @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k1_funct_1 @ X21 @ ( k1_funct_1 @ X22 @ X23 ) ) )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_5 @ X0 ) @ ( sk_C_4 @ sk_C_5 @ ( k1_relat_1 @ sk_C_5 ) ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) )
      | ( sk_C_5
        = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_5 ) ) )
      | ~ ( v1_funct_1 @ sk_C_5 )
      | ~ ( v1_relat_1 @ sk_C_5 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_5 @ X0 ) @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) )
      | ( sk_C_5
        = ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    sk_C_5
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_5 @ X0 ) @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X25
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ X25 @ ( k1_relat_1 @ X25 ) ) @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ ( k1_relat_1 @ sk_C_5 ) )
    | ( sk_C_5
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_5 ) ) )
    | ~ ( v1_funct_1 @ sk_C_5 )
    | ~ ( v1_relat_1 @ sk_C_5 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_A )
    | ( sk_C_5
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    sk_C_5
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('26',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ ( sk_D_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ ( sk_D_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['23','27'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_D_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_D_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_B_1 )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['28','34'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k2_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X15 @ X13 ) @ X15 ) @ X13 )
      | ( X14
       != ( k2_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('40',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X15 @ X13 ) @ X15 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_funct_1 @ X18 @ X19 )
       != ( k1_funct_1 @ X18 @ X20 ) )
      | ( X19 = X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) @ sk_A )
      | ( X0
        = ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','40'])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    r2_hidden @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r2_hidden @ ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) )
      | ( X0
        = ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) )
      | ( X0
        = ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_A )
    | ( ( sk_C_4 @ sk_C_5 @ sk_A )
      = ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference(eq_res,[status(thm)],['63'])).

thf('65',plain,(
    r2_hidden @ ( sk_C_4 @ sk_C_5 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('66',plain,
    ( ( sk_C_4 @ sk_C_5 @ sk_A )
    = ( sk_D_3 @ ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) )
      | ( X0
        = ( sk_C_4 @ sk_C_5 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_5 @ sk_B_1 ) @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_A )
    | ( ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
      = ( sk_C_4 @ sk_C_5 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_C_5 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X25
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ X25 @ ( k1_relat_1 @ X25 ) ) @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('73',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ X28 )
      | ( X29
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D_1 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_4 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_5 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ~ ( v1_funct_1 @ sk_C_5 )
    | ( sk_C_5
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_5 ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ ( k1_relat_1 @ sk_C_5 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_C_5
      = ( k6_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
    sk_C_5
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
     != ( k1_funct_1 @ sk_B_1 @ ( sk_C_4 @ sk_C_5 @ sk_A ) ) )
    | ( ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
      = ( sk_C_4 @ sk_C_5 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','93'])).

thf('95',plain,
    ( ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
    = ( sk_C_4 @ sk_C_5 @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != X24 )
      | ( ( k1_funct_1 @ X25 @ ( sk_C_4 @ X25 @ X24 ) )
       != ( sk_C_4 @ X25 @ X24 ) )
      | ( X25
        = ( k6_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('98',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X25
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ( ( k1_funct_1 @ X25 @ ( sk_C_4 @ X25 @ ( k1_relat_1 @ X25 ) ) )
       != ( sk_C_4 @ X25 @ ( k1_relat_1 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
     != ( sk_C_4 @ sk_C_5 @ ( k1_relat_1 @ sk_C_5 ) ) )
    | ( sk_C_5
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_5 ) ) )
    | ~ ( v1_funct_1 @ sk_C_5 )
    | ~ ( v1_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C_5 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
     != ( sk_C_4 @ sk_C_5 @ sk_A ) )
    | ( sk_C_5
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,(
    sk_C_5
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ( k1_funct_1 @ sk_C_5 @ ( sk_C_4 @ sk_C_5 @ sk_A ) )
 != ( sk_C_4 @ sk_C_5 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0HMo6wjZC4
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 24.32/24.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.32/24.52  % Solved by: fo/fo7.sh
% 24.32/24.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.32/24.52  % done 19715 iterations in 24.062s
% 24.32/24.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.32/24.52  % SZS output start Refutation
% 24.32/24.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 24.32/24.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 24.32/24.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 24.32/24.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 24.32/24.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 24.32/24.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 24.32/24.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 24.32/24.52  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 24.32/24.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 24.32/24.52  thf(sk_A_type, type, sk_A: $i).
% 24.32/24.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.32/24.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 24.32/24.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 24.32/24.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 24.32/24.52  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 24.32/24.52  thf(sk_C_5_type, type, sk_C_5: $i).
% 24.32/24.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 24.32/24.52  thf(t50_funct_1, conjecture,
% 24.32/24.52    (![A:$i,B:$i]:
% 24.32/24.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 24.32/24.52       ( ![C:$i]:
% 24.32/24.52         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 24.32/24.52           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 24.32/24.52               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 24.32/24.52               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 24.32/24.52               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 24.32/24.52             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 24.32/24.52  thf(zf_stmt_0, negated_conjecture,
% 24.32/24.52    (~( ![A:$i,B:$i]:
% 24.32/24.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 24.32/24.52          ( ![C:$i]:
% 24.32/24.52            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 24.32/24.52              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 24.32/24.52                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 24.32/24.52                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 24.32/24.52                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 24.32/24.52                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 24.32/24.52    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 24.32/24.52  thf('0', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf(t34_funct_1, axiom,
% 24.32/24.52    (![A:$i,B:$i]:
% 24.32/24.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 24.32/24.52       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 24.32/24.52         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 24.32/24.52           ( ![C:$i]:
% 24.32/24.52             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 24.32/24.52  thf('1', plain,
% 24.32/24.52      (![X24 : $i, X25 : $i]:
% 24.32/24.52         (((k1_relat_1 @ X25) != (X24))
% 24.32/24.52          | (r2_hidden @ (sk_C_4 @ X25 @ X24) @ X24)
% 24.32/24.52          | ((X25) = (k6_relat_1 @ X24))
% 24.32/24.52          | ~ (v1_funct_1 @ X25)
% 24.32/24.52          | ~ (v1_relat_1 @ X25))),
% 24.32/24.52      inference('cnf', [status(esa)], [t34_funct_1])).
% 24.32/24.52  thf('2', plain,
% 24.32/24.52      (![X25 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X25)
% 24.32/24.52          | ~ (v1_funct_1 @ X25)
% 24.32/24.52          | ((X25) = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 24.32/24.52          | (r2_hidden @ (sk_C_4 @ X25 @ (k1_relat_1 @ X25)) @ 
% 24.32/24.52             (k1_relat_1 @ X25)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['1'])).
% 24.32/24.52  thf(t23_funct_1, axiom,
% 24.32/24.52    (![A:$i,B:$i]:
% 24.32/24.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 24.32/24.52       ( ![C:$i]:
% 24.32/24.52         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 24.32/24.52           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 24.32/24.52             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 24.32/24.52               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 24.32/24.52  thf('3', plain,
% 24.32/24.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X21)
% 24.32/24.52          | ~ (v1_funct_1 @ X21)
% 24.32/24.52          | ((k1_funct_1 @ (k5_relat_1 @ X22 @ X21) @ X23)
% 24.32/24.52              = (k1_funct_1 @ X21 @ (k1_funct_1 @ X22 @ X23)))
% 24.32/24.52          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 24.32/24.52          | ~ (v1_funct_1 @ X22)
% 24.32/24.52          | ~ (v1_relat_1 @ X22))),
% 24.32/24.52      inference('cnf', [status(esa)], [t23_funct_1])).
% 24.32/24.52  thf('4', plain,
% 24.32/24.52      (![X0 : $i, X1 : $i]:
% 24.32/24.52         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 24.32/24.52              (sk_C_4 @ X0 @ (k1_relat_1 @ X0)))
% 24.32/24.52              = (k1_funct_1 @ X1 @ 
% 24.32/24.52                 (k1_funct_1 @ X0 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)))))
% 24.32/24.52          | ~ (v1_funct_1 @ X1)
% 24.32/24.52          | ~ (v1_relat_1 @ X1))),
% 24.32/24.52      inference('sup-', [status(thm)], ['2', '3'])).
% 24.32/24.52  thf('5', plain,
% 24.32/24.52      (![X0 : $i, X1 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X1)
% 24.32/24.52          | ~ (v1_funct_1 @ X1)
% 24.32/24.52          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 24.32/24.52              (sk_C_4 @ X0 @ (k1_relat_1 @ X0)))
% 24.32/24.52              = (k1_funct_1 @ X1 @ 
% 24.32/24.52                 (k1_funct_1 @ X0 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)))))
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 24.32/24.52      inference('simplify', [status(thm)], ['4'])).
% 24.32/24.52  thf('6', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ (k5_relat_1 @ sk_C_5 @ X0) @ 
% 24.32/24.52            (sk_C_4 @ sk_C_5 @ (k1_relat_1 @ sk_C_5)))
% 24.32/24.52            = (k1_funct_1 @ X0 @ 
% 24.32/24.52               (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))))
% 24.32/24.52          | ((sk_C_5) = (k6_relat_1 @ (k1_relat_1 @ sk_C_5)))
% 24.32/24.52          | ~ (v1_funct_1 @ sk_C_5)
% 24.32/24.52          | ~ (v1_relat_1 @ sk_C_5)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0))),
% 24.32/24.52      inference('sup+', [status(thm)], ['0', '5'])).
% 24.32/24.52  thf('7', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('8', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('9', plain, ((v1_funct_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('10', plain, ((v1_relat_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('11', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ (k5_relat_1 @ sk_C_5 @ X0) @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52            = (k1_funct_1 @ X0 @ 
% 24.32/24.52               (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))))
% 24.32/24.52          | ((sk_C_5) = (k6_relat_1 @ sk_A))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0))),
% 24.32/24.52      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 24.32/24.52  thf('12', plain, (((sk_C_5) != (k6_relat_1 @ sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('13', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ (k5_relat_1 @ sk_C_5 @ X0) @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52            = (k1_funct_1 @ X0 @ 
% 24.32/24.52               (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0))),
% 24.32/24.52      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 24.32/24.52  thf('14', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('15', plain,
% 24.32/24.52      (![X25 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X25)
% 24.32/24.52          | ~ (v1_funct_1 @ X25)
% 24.32/24.52          | ((X25) = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 24.32/24.52          | (r2_hidden @ (sk_C_4 @ X25 @ (k1_relat_1 @ X25)) @ 
% 24.32/24.52             (k1_relat_1 @ X25)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['1'])).
% 24.32/24.52  thf('16', plain,
% 24.32/24.52      (((r2_hidden @ (sk_C_4 @ sk_C_5 @ sk_A) @ (k1_relat_1 @ sk_C_5))
% 24.32/24.52        | ((sk_C_5) = (k6_relat_1 @ (k1_relat_1 @ sk_C_5)))
% 24.32/24.52        | ~ (v1_funct_1 @ sk_C_5)
% 24.32/24.52        | ~ (v1_relat_1 @ sk_C_5))),
% 24.32/24.52      inference('sup+', [status(thm)], ['14', '15'])).
% 24.32/24.52  thf('17', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('18', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('19', plain, ((v1_funct_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('20', plain, ((v1_relat_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('21', plain,
% 24.32/24.52      (((r2_hidden @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_A)
% 24.32/24.52        | ((sk_C_5) = (k6_relat_1 @ sk_A)))),
% 24.32/24.52      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 24.32/24.52  thf('22', plain, (((sk_C_5) != (k6_relat_1 @ sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('23', plain, ((r2_hidden @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_A)),
% 24.32/24.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 24.32/24.52  thf('24', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf(d4_relat_1, axiom,
% 24.32/24.52    (![A:$i,B:$i]:
% 24.32/24.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 24.32/24.52       ( ![C:$i]:
% 24.32/24.52         ( ( r2_hidden @ C @ B ) <=>
% 24.32/24.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 24.32/24.52  thf('25', plain,
% 24.32/24.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 24.32/24.52         (~ (r2_hidden @ X8 @ X7)
% 24.32/24.52          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 24.32/24.52          | ((X7) != (k1_relat_1 @ X6)))),
% 24.32/24.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 24.32/24.52  thf('26', plain,
% 24.32/24.52      (![X6 : $i, X8 : $i]:
% 24.32/24.52         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 24.32/24.52          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['25'])).
% 24.32/24.52  thf('27', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (~ (r2_hidden @ X0 @ sk_A)
% 24.32/24.52          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_B_1)) @ sk_B_1))),
% 24.32/24.52      inference('sup-', [status(thm)], ['24', '26'])).
% 24.32/24.52  thf('28', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (k4_tarski @ (sk_C_4 @ sk_C_5 @ sk_A) @ 
% 24.32/24.52         (sk_D_1 @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_B_1)) @ 
% 24.32/24.52        sk_B_1)),
% 24.32/24.52      inference('sup-', [status(thm)], ['23', '27'])).
% 24.32/24.52  thf('29', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (k4_tarski @ (sk_C_4 @ sk_C_5 @ sk_A) @ 
% 24.32/24.52         (sk_D_1 @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_B_1)) @ 
% 24.32/24.52        sk_B_1)),
% 24.32/24.52      inference('sup-', [status(thm)], ['23', '27'])).
% 24.32/24.52  thf(t8_funct_1, axiom,
% 24.32/24.52    (![A:$i,B:$i,C:$i]:
% 24.32/24.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 24.32/24.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 24.32/24.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 24.32/24.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 24.32/24.52  thf('30', plain,
% 24.32/24.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 24.32/24.52         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 24.32/24.52          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 24.32/24.52          | ~ (v1_funct_1 @ X28)
% 24.32/24.52          | ~ (v1_relat_1 @ X28))),
% 24.32/24.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 24.32/24.52  thf('31', plain,
% 24.32/24.52      ((~ (v1_relat_1 @ sk_B_1)
% 24.32/24.52        | ~ (v1_funct_1 @ sk_B_1)
% 24.32/24.52        | ((sk_D_1 @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_B_1)
% 24.32/24.52            = (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))))),
% 24.32/24.52      inference('sup-', [status(thm)], ['29', '30'])).
% 24.32/24.52  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('34', plain,
% 24.32/24.52      (((sk_D_1 @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_B_1)
% 24.32/24.52         = (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))),
% 24.32/24.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 24.32/24.52  thf('35', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (k4_tarski @ (sk_C_4 @ sk_C_5 @ sk_A) @ 
% 24.32/24.52         (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))) @ 
% 24.32/24.52        sk_B_1)),
% 24.32/24.52      inference('demod', [status(thm)], ['28', '34'])).
% 24.32/24.52  thf(d5_relat_1, axiom,
% 24.32/24.52    (![A:$i,B:$i]:
% 24.32/24.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 24.32/24.52       ( ![C:$i]:
% 24.32/24.52         ( ( r2_hidden @ C @ B ) <=>
% 24.32/24.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 24.32/24.52  thf('36', plain,
% 24.32/24.52      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 24.32/24.52         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 24.32/24.52          | (r2_hidden @ X12 @ X14)
% 24.32/24.52          | ((X14) != (k2_relat_1 @ X13)))),
% 24.32/24.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 24.32/24.52  thf('37', plain,
% 24.32/24.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 24.32/24.52         ((r2_hidden @ X12 @ (k2_relat_1 @ X13))
% 24.32/24.52          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 24.32/24.52      inference('simplify', [status(thm)], ['36'])).
% 24.32/24.52  thf('38', plain,
% 24.32/24.52      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52        (k2_relat_1 @ sk_B_1))),
% 24.32/24.52      inference('sup-', [status(thm)], ['35', '37'])).
% 24.32/24.52  thf('39', plain,
% 24.32/24.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.32/24.52         (~ (r2_hidden @ X15 @ X14)
% 24.32/24.52          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X15 @ X13) @ X15) @ X13)
% 24.32/24.52          | ((X14) != (k2_relat_1 @ X13)))),
% 24.32/24.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 24.32/24.52  thf('40', plain,
% 24.32/24.52      (![X13 : $i, X15 : $i]:
% 24.32/24.52         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X15 @ X13) @ X15) @ X13)
% 24.32/24.52          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X13)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['39'])).
% 24.32/24.52  thf('41', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (k4_tarski @ 
% 24.32/24.52         (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_B_1) @ 
% 24.32/24.52         (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))) @ 
% 24.32/24.52        sk_B_1)),
% 24.32/24.52      inference('sup-', [status(thm)], ['38', '40'])).
% 24.32/24.52  thf('42', plain,
% 24.32/24.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 24.32/24.52         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 24.32/24.52          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 24.32/24.52          | ~ (v1_funct_1 @ X28)
% 24.32/24.52          | ~ (v1_relat_1 @ X28))),
% 24.32/24.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 24.32/24.52  thf('43', plain,
% 24.32/24.52      ((~ (v1_relat_1 @ sk_B_1)
% 24.32/24.52        | ~ (v1_funct_1 @ sk_B_1)
% 24.32/24.52        | ((k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52            = (k1_funct_1 @ sk_B_1 @ 
% 24.32/24.52               (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52                sk_B_1))))),
% 24.32/24.52      inference('sup-', [status(thm)], ['41', '42'])).
% 24.32/24.52  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('46', plain,
% 24.32/24.52      (((k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52         = (k1_funct_1 @ sk_B_1 @ 
% 24.32/24.52            (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_B_1)))),
% 24.32/24.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 24.32/24.52  thf('47', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf(d8_funct_1, axiom,
% 24.32/24.52    (![A:$i]:
% 24.32/24.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 24.32/24.52       ( ( v2_funct_1 @ A ) <=>
% 24.32/24.52         ( ![B:$i,C:$i]:
% 24.32/24.52           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 24.32/24.52               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 24.32/24.52               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 24.32/24.52             ( ( B ) = ( C ) ) ) ) ) ))).
% 24.32/24.52  thf('48', plain,
% 24.32/24.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 24.32/24.52         (~ (v2_funct_1 @ X18)
% 24.32/24.52          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X18))
% 24.32/24.52          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X18))
% 24.32/24.52          | ((k1_funct_1 @ X18 @ X19) != (k1_funct_1 @ X18 @ X20))
% 24.32/24.52          | ((X19) = (X20))
% 24.32/24.52          | ~ (v1_funct_1 @ X18)
% 24.32/24.52          | ~ (v1_relat_1 @ X18))),
% 24.32/24.52      inference('cnf', [status(esa)], [d8_funct_1])).
% 24.32/24.52  thf('49', plain,
% 24.32/24.52      (![X0 : $i, X1 : $i]:
% 24.32/24.52         (~ (r2_hidden @ X0 @ sk_A)
% 24.32/24.52          | ~ (v1_relat_1 @ sk_B_1)
% 24.32/24.52          | ~ (v1_funct_1 @ sk_B_1)
% 24.32/24.52          | ((X0) = (X1))
% 24.32/24.52          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 24.32/24.52          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 24.32/24.52          | ~ (v2_funct_1 @ sk_B_1))),
% 24.32/24.52      inference('sup-', [status(thm)], ['47', '48'])).
% 24.32/24.52  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('51', plain, ((v1_funct_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('52', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('53', plain, ((v2_funct_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('54', plain,
% 24.32/24.52      (![X0 : $i, X1 : $i]:
% 24.32/24.52         (~ (r2_hidden @ X0 @ sk_A)
% 24.32/24.52          | ((X0) = (X1))
% 24.32/24.52          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 24.32/24.52          | ~ (r2_hidden @ X1 @ sk_A))),
% 24.32/24.52      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 24.32/24.52  thf('55', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ sk_B_1 @ X0)
% 24.32/24.52            != (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))
% 24.32/24.52          | ~ (r2_hidden @ 
% 24.32/24.52               (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52                sk_B_1) @ 
% 24.32/24.52               sk_A)
% 24.32/24.52          | ((X0)
% 24.32/24.52              = (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52                 sk_B_1))
% 24.32/24.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 24.32/24.52      inference('sup-', [status(thm)], ['46', '54'])).
% 24.32/24.52  thf('56', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (k4_tarski @ 
% 24.32/24.52         (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_B_1) @ 
% 24.32/24.52         (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))) @ 
% 24.32/24.52        sk_B_1)),
% 24.32/24.52      inference('sup-', [status(thm)], ['38', '40'])).
% 24.32/24.52  thf('57', plain,
% 24.32/24.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 24.32/24.52         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 24.32/24.52          | (r2_hidden @ X4 @ X7)
% 24.32/24.52          | ((X7) != (k1_relat_1 @ X6)))),
% 24.32/24.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 24.32/24.52  thf('58', plain,
% 24.32/24.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.32/24.52         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 24.32/24.52          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 24.32/24.52      inference('simplify', [status(thm)], ['57'])).
% 24.32/24.52  thf('59', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_B_1) @ 
% 24.32/24.52        (k1_relat_1 @ sk_B_1))),
% 24.32/24.52      inference('sup-', [status(thm)], ['56', '58'])).
% 24.32/24.52  thf('60', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('61', plain,
% 24.32/24.52      ((r2_hidden @ 
% 24.32/24.52        (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_B_1) @ 
% 24.32/24.52        sk_A)),
% 24.32/24.52      inference('demod', [status(thm)], ['59', '60'])).
% 24.32/24.52  thf('62', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ sk_B_1 @ X0)
% 24.32/24.52            != (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))
% 24.32/24.52          | ((X0)
% 24.32/24.52              = (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52                 sk_B_1))
% 24.32/24.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 24.32/24.52      inference('demod', [status(thm)], ['55', '61'])).
% 24.32/24.52  thf('63', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ sk_B_1 @ X0)
% 24.32/24.52            != (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))
% 24.32/24.52          | ((X0)
% 24.32/24.52              = (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52                 sk_B_1))
% 24.32/24.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 24.32/24.52      inference('demod', [status(thm)], ['55', '61'])).
% 24.32/24.52  thf('64', plain,
% 24.32/24.52      ((~ (r2_hidden @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_A)
% 24.32/24.52        | ((sk_C_4 @ sk_C_5 @ sk_A)
% 24.32/24.52            = (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52               sk_B_1)))),
% 24.32/24.52      inference('eq_res', [status(thm)], ['63'])).
% 24.32/24.52  thf('65', plain, ((r2_hidden @ (sk_C_4 @ sk_C_5 @ sk_A) @ sk_A)),
% 24.32/24.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 24.32/24.52  thf('66', plain,
% 24.32/24.52      (((sk_C_4 @ sk_C_5 @ sk_A)
% 24.32/24.52         = (sk_D_3 @ (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_B_1))),
% 24.32/24.52      inference('demod', [status(thm)], ['64', '65'])).
% 24.32/24.52  thf('67', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((k1_funct_1 @ sk_B_1 @ X0)
% 24.32/24.52            != (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))
% 24.32/24.52          | ((X0) = (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 24.32/24.52      inference('demod', [status(thm)], ['62', '66'])).
% 24.32/24.52  thf('68', plain,
% 24.32/24.52      ((((k1_funct_1 @ (k5_relat_1 @ sk_C_5 @ sk_B_1) @ 
% 24.32/24.52          (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52          != (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))
% 24.32/24.52        | ~ (v1_relat_1 @ sk_B_1)
% 24.32/24.52        | ~ (v1_funct_1 @ sk_B_1)
% 24.32/24.52        | ~ (r2_hidden @ (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ 
% 24.32/24.52             sk_A)
% 24.32/24.52        | ((k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52            = (sk_C_4 @ sk_C_5 @ sk_A)))),
% 24.32/24.52      inference('sup-', [status(thm)], ['13', '67'])).
% 24.32/24.52  thf('69', plain, (((k5_relat_1 @ sk_C_5 @ sk_B_1) = (sk_B_1))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('71', plain, ((v1_funct_1 @ sk_B_1)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('72', plain,
% 24.32/24.52      (![X25 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X25)
% 24.32/24.52          | ~ (v1_funct_1 @ X25)
% 24.32/24.52          | ((X25) = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 24.32/24.52          | (r2_hidden @ (sk_C_4 @ X25 @ (k1_relat_1 @ X25)) @ 
% 24.32/24.52             (k1_relat_1 @ X25)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['1'])).
% 24.32/24.52  thf('73', plain,
% 24.32/24.52      (![X6 : $i, X8 : $i]:
% 24.32/24.52         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 24.32/24.52          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['25'])).
% 24.32/24.52  thf('74', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | (r2_hidden @ 
% 24.32/24.52             (k4_tarski @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ 
% 24.32/24.52              (sk_D_1 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 24.32/24.52             X0))),
% 24.32/24.52      inference('sup-', [status(thm)], ['72', '73'])).
% 24.32/24.52  thf('75', plain,
% 24.32/24.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 24.32/24.52         (~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ X28)
% 24.32/24.52          | ((X29) = (k1_funct_1 @ X28 @ X27))
% 24.32/24.52          | ~ (v1_funct_1 @ X28)
% 24.32/24.52          | ~ (v1_relat_1 @ X28))),
% 24.32/24.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 24.32/24.52  thf('76', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ((sk_D_1 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ X0)
% 24.32/24.52              = (k1_funct_1 @ X0 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)))))),
% 24.32/24.52      inference('sup-', [status(thm)], ['74', '75'])).
% 24.32/24.52  thf('77', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((sk_D_1 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ X0)
% 24.32/24.52            = (k1_funct_1 @ X0 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0))))
% 24.32/24.52          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0))),
% 24.32/24.52      inference('simplify', [status(thm)], ['76'])).
% 24.32/24.52  thf('78', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | (r2_hidden @ 
% 24.32/24.52             (k4_tarski @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ 
% 24.32/24.52              (sk_D_1 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 24.32/24.52             X0))),
% 24.32/24.52      inference('sup-', [status(thm)], ['72', '73'])).
% 24.32/24.52  thf('79', plain,
% 24.32/24.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 24.32/24.52         ((r2_hidden @ X12 @ (k2_relat_1 @ X13))
% 24.32/24.52          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 24.32/24.52      inference('simplify', [status(thm)], ['36'])).
% 24.32/24.52  thf('80', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | (r2_hidden @ (sk_D_1 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0)) @ X0) @ 
% 24.32/24.52             (k2_relat_1 @ X0)))),
% 24.32/24.52      inference('sup-', [status(thm)], ['78', '79'])).
% 24.32/24.52  thf('81', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0))) @ 
% 24.32/24.52           (k2_relat_1 @ X0))
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0))),
% 24.32/24.52      inference('sup+', [status(thm)], ['77', '80'])).
% 24.32/24.52  thf('82', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 24.32/24.52          | ~ (v1_funct_1 @ X0)
% 24.32/24.52          | ~ (v1_relat_1 @ X0)
% 24.32/24.52          | (r2_hidden @ 
% 24.32/24.52             (k1_funct_1 @ X0 @ (sk_C_4 @ X0 @ (k1_relat_1 @ X0))) @ 
% 24.32/24.52             (k2_relat_1 @ X0)))),
% 24.32/24.52      inference('simplify', [status(thm)], ['81'])).
% 24.32/24.52  thf('83', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_5) @ sk_A)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf(d3_tarski, axiom,
% 24.32/24.52    (![A:$i,B:$i]:
% 24.32/24.52     ( ( r1_tarski @ A @ B ) <=>
% 24.32/24.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 24.32/24.52  thf('84', plain,
% 24.32/24.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.32/24.52         (~ (r2_hidden @ X0 @ X1)
% 24.32/24.52          | (r2_hidden @ X0 @ X2)
% 24.32/24.52          | ~ (r1_tarski @ X1 @ X2))),
% 24.32/24.52      inference('cnf', [status(esa)], [d3_tarski])).
% 24.32/24.52  thf('85', plain,
% 24.32/24.52      (![X0 : $i]:
% 24.32/24.52         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_5)))),
% 24.32/24.52      inference('sup-', [status(thm)], ['83', '84'])).
% 24.32/24.52  thf('86', plain,
% 24.32/24.52      ((~ (v1_relat_1 @ sk_C_5)
% 24.32/24.52        | ~ (v1_funct_1 @ sk_C_5)
% 24.32/24.52        | ((sk_C_5) = (k6_relat_1 @ (k1_relat_1 @ sk_C_5)))
% 24.32/24.52        | (r2_hidden @ 
% 24.32/24.52           (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ (k1_relat_1 @ sk_C_5))) @ 
% 24.32/24.52           sk_A))),
% 24.32/24.52      inference('sup-', [status(thm)], ['82', '85'])).
% 24.32/24.52  thf('87', plain, ((v1_relat_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('88', plain, ((v1_funct_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('89', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('90', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('91', plain,
% 24.32/24.52      ((((sk_C_5) = (k6_relat_1 @ sk_A))
% 24.32/24.52        | (r2_hidden @ (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_A))),
% 24.32/24.52      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 24.32/24.52  thf('92', plain, (((sk_C_5) != (k6_relat_1 @ sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('93', plain,
% 24.32/24.52      ((r2_hidden @ (k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A)) @ sk_A)),
% 24.32/24.52      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 24.32/24.52  thf('94', plain,
% 24.32/24.52      ((((k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52          != (k1_funct_1 @ sk_B_1 @ (sk_C_4 @ sk_C_5 @ sk_A)))
% 24.32/24.52        | ((k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52            = (sk_C_4 @ sk_C_5 @ sk_A)))),
% 24.32/24.52      inference('demod', [status(thm)], ['68', '69', '70', '71', '93'])).
% 24.32/24.52  thf('95', plain,
% 24.32/24.52      (((k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52         = (sk_C_4 @ sk_C_5 @ sk_A))),
% 24.32/24.52      inference('simplify', [status(thm)], ['94'])).
% 24.32/24.52  thf('96', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('97', plain,
% 24.32/24.52      (![X24 : $i, X25 : $i]:
% 24.32/24.52         (((k1_relat_1 @ X25) != (X24))
% 24.32/24.52          | ((k1_funct_1 @ X25 @ (sk_C_4 @ X25 @ X24)) != (sk_C_4 @ X25 @ X24))
% 24.32/24.52          | ((X25) = (k6_relat_1 @ X24))
% 24.32/24.52          | ~ (v1_funct_1 @ X25)
% 24.32/24.52          | ~ (v1_relat_1 @ X25))),
% 24.32/24.52      inference('cnf', [status(esa)], [t34_funct_1])).
% 24.32/24.52  thf('98', plain,
% 24.32/24.52      (![X25 : $i]:
% 24.32/24.52         (~ (v1_relat_1 @ X25)
% 24.32/24.52          | ~ (v1_funct_1 @ X25)
% 24.32/24.52          | ((X25) = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 24.32/24.52          | ((k1_funct_1 @ X25 @ (sk_C_4 @ X25 @ (k1_relat_1 @ X25)))
% 24.32/24.52              != (sk_C_4 @ X25 @ (k1_relat_1 @ X25))))),
% 24.32/24.52      inference('simplify', [status(thm)], ['97'])).
% 24.32/24.52  thf('99', plain,
% 24.32/24.52      ((((k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52          != (sk_C_4 @ sk_C_5 @ (k1_relat_1 @ sk_C_5)))
% 24.32/24.52        | ((sk_C_5) = (k6_relat_1 @ (k1_relat_1 @ sk_C_5)))
% 24.32/24.52        | ~ (v1_funct_1 @ sk_C_5)
% 24.32/24.52        | ~ (v1_relat_1 @ sk_C_5))),
% 24.32/24.52      inference('sup-', [status(thm)], ['96', '98'])).
% 24.32/24.52  thf('100', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('101', plain, (((k1_relat_1 @ sk_C_5) = (sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('102', plain, ((v1_funct_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('103', plain, ((v1_relat_1 @ sk_C_5)),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('104', plain,
% 24.32/24.52      ((((k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52          != (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52        | ((sk_C_5) = (k6_relat_1 @ sk_A)))),
% 24.32/24.52      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 24.32/24.52  thf('105', plain, (((sk_C_5) != (k6_relat_1 @ sk_A))),
% 24.32/24.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.52  thf('106', plain,
% 24.32/24.52      (((k1_funct_1 @ sk_C_5 @ (sk_C_4 @ sk_C_5 @ sk_A))
% 24.32/24.52         != (sk_C_4 @ sk_C_5 @ sk_A))),
% 24.32/24.52      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 24.32/24.52  thf('107', plain, ($false),
% 24.32/24.52      inference('simplify_reflect-', [status(thm)], ['95', '106'])).
% 24.32/24.52  
% 24.32/24.52  % SZS output end Refutation
% 24.32/24.52  
% 24.32/24.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
