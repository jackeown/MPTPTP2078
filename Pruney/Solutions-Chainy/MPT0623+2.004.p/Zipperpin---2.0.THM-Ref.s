%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.trwUcJ2jEz

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:36 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 979 expanded)
%              Number of leaves         :   27 ( 286 expanded)
%              Depth                    :   28
%              Number of atoms          : 1060 (9061 expanded)
%              Number of equality atoms :  129 (1370 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
        = X22 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

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

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 ) ) ),
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

thf('7',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X15 @ X14 ) @ X14 )
      | ( X14
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
        = X22 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','50'])).

thf('52',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ X20 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
       != ( k1_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('64',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('70',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65','70'])).

thf('72',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['52'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','83'])).

thf('85',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_tarski @ X1 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ X1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( sk_C_2 @ X1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ X2 )
      | ( sk_A
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','83'])).

thf('91',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_tarski @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X1 @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','83'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( sk_A
        = ( k1_tarski @ X1 ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference(clc,[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ sk_A ) ),
    inference(eq_fact,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ~ ( r1_xboole_0 @ X0 @ X2 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X1 @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['13','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.trwUcJ2jEz
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 335 iterations in 0.236s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.70  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.45/0.70  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.70  thf(t15_funct_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ?[C:$i]:
% 0.45/0.70           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.45/0.70             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.45/0.70             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.45/0.70  thf('0', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (sk_C_3 @ X21 @ X22)) = (X22))
% 0.45/0.70          | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         ((v1_relat_1 @ (sk_C_3 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         ((v1_funct_1 @ (sk_C_3 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf(t3_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.70            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.70  thf(l1_zfmisc_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X9 : $i, X11 : $i]:
% 0.45/0.70         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.70  thf('5', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ X0 @ X1)
% 0.45/0.70          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X1 @ X0)) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         (((k2_relat_1 @ (sk_C_3 @ X21 @ X22)) = (k1_tarski @ X21))
% 0.45/0.70          | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf(t18_funct_1, conjecture,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.70          ( ![C:$i]:
% 0.45/0.70            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.70              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.45/0.70                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i,B:$i]:
% 0.45/0.70        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.70             ( ![C:$i]:
% 0.45/0.70               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.70                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.45/0.70                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (![X23 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ X23))
% 0.45/0.70          | ~ (v1_funct_1 @ X23)
% 0.45/0.70          | ~ (v1_relat_1 @ X23))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.45/0.70          | ((X1) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.45/0.70          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ sk_A @ X0)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X0 @ sk_A) @ X1)))
% 0.45/0.70          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C_1 @ X0 @ sk_A) @ X1))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X0 @ sk_A) @ X1))
% 0.45/0.70          | ((X1) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.70  thf('10', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_xboole_0))
% 0.45/0.70          | ((X0) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | (r1_xboole_0 @ sk_A @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['2', '9'])).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ sk_A @ X1)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0))
% 0.45/0.70          | ((X0) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_xboole_0))
% 0.45/0.70          | ((X0) = (k1_xboole_0))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | (r1_xboole_0 @ sk_A @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['1', '11'])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ sk_A @ X1)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | ((X0) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.70  thf('15', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.70  thf(d3_tarski, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.70          | (r2_hidden @ X0 @ X2)
% 0.45/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.70          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.70  thf(l44_zfmisc_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.70          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X14 : $i, X15 : $i]:
% 0.45/0.70         (((X14) = (k1_xboole_0))
% 0.45/0.70          | (r2_hidden @ (sk_C_2 @ X15 @ X14) @ X14)
% 0.45/0.70          | ((X14) = (k1_tarski @ X15)))),
% 0.45/0.70      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         (((k1_relat_1 @ (sk_C_3 @ X21 @ X22)) = (X22))
% 0.45/0.70          | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         ((v1_relat_1 @ (sk_C_3 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i]:
% 0.45/0.70         ((v1_funct_1 @ (sk_C_3 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X1 : $i, X3 : $i]:
% 0.45/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (![X9 : $i, X11 : $i]:
% 0.45/0.70         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_tarski @ X0 @ X1)
% 0.45/0.70          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.45/0.70          | ((X1) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.45/0.70          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_tarski @ sk_A @ X0)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.45/0.70          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.45/0.70          | ((X1) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_xboole_0))
% 0.45/0.70          | ((X0) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | (r1_tarski @ sk_A @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['22', '27'])).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_tarski @ sk_A @ X1)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.45/0.70          | ((X0) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_xboole_0))
% 0.45/0.70          | ((X0) = (k1_xboole_0))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | (r1_tarski @ sk_A @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['21', '29'])).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r1_tarski @ sk_A @ X1)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.45/0.70          | ((X0) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((sk_B) != (X0))
% 0.45/0.70          | ((X0) = (k1_xboole_0))
% 0.45/0.70          | ((X0) = (k1_xboole_0))
% 0.45/0.70          | (r1_tarski @ sk_A @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['20', '31'])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.70  thf(cc1_funct_1, axiom,
% 0.45/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.45/0.70  thf('34', plain, (![X20 : $i]: ((v1_funct_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.45/0.70  thf(cc1_relat_1, axiom,
% 0.45/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.45/0.70  thf('35', plain, (![X19 : $i]: ((v1_relat_1 @ X19) | ~ (v1_xboole_0 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.45/0.70  thf(t60_relat_1, axiom,
% 0.45/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.70  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      (![X23 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ X23))
% 0.45/0.70          | ~ (v1_funct_1 @ X23)
% 0.45/0.70          | ~ (v1_relat_1 @ X23))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.45/0.70        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.70        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.70        | ((sk_B) != (k1_relat_1 @ k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.70  thf('39', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.70  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.70  thf('41', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.70        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.70        | ((sk_B) != (k1_xboole_0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.45/0.70  thf('42', plain,
% 0.45/0.70      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.70        | ((sk_B) != (k1_xboole_0))
% 0.45/0.70        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['35', '41'])).
% 0.45/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.70  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      ((((sk_B) != (k1_xboole_0)) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) != (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['34', '44'])).
% 0.45/0.70  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.70  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.70  thf('48', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['33', '47'])).
% 0.45/0.70  thf('49', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.70          | (r2_hidden @ X0 @ X2)
% 0.45/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.70  thf('50', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.70  thf('51', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X0))
% 0.45/0.70          | ((sk_A) = (k1_xboole_0))
% 0.45/0.70          | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['19', '50'])).
% 0.45/0.70  thf('52', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('53', plain,
% 0.45/0.70      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('54', plain, (![X19 : $i]: ((v1_relat_1 @ X19) | ~ (v1_xboole_0 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.45/0.70  thf('55', plain, (![X20 : $i]: ((v1_funct_1 @ X20) | ~ (v1_xboole_0 @ X20))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.45/0.70  thf('56', plain,
% 0.45/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.70  thf('58', plain,
% 0.45/0.70      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup+', [status(thm)], ['56', '57'])).
% 0.45/0.70  thf('59', plain,
% 0.45/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('60', plain,
% 0.45/0.70      ((((k2_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.70  thf('61', plain,
% 0.45/0.70      (![X23 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ X23))
% 0.45/0.70          | ~ (v1_funct_1 @ X23)
% 0.45/0.70          | ~ (v1_relat_1 @ X23))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('62', plain,
% 0.45/0.70      (((~ (r1_tarski @ sk_B @ sk_A)
% 0.45/0.70         | ~ (v1_relat_1 @ sk_B)
% 0.45/0.70         | ~ (v1_funct_1 @ sk_B)
% 0.45/0.70         | ((sk_B) != (k1_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.70  thf('63', plain,
% 0.45/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('64', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.70  thf('65', plain,
% 0.45/0.70      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup+', [status(thm)], ['63', '64'])).
% 0.45/0.70  thf('66', plain,
% 0.45/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.70  thf('68', plain,
% 0.45/0.70      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup+', [status(thm)], ['66', '67'])).
% 0.45/0.70  thf('69', plain,
% 0.45/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('70', plain,
% 0.45/0.70      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.70  thf('71', plain,
% 0.45/0.70      (((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ((sk_B) != (sk_B))))
% 0.45/0.70         <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('demod', [status(thm)], ['62', '65', '70'])).
% 0.45/0.70  thf('72', plain,
% 0.45/0.70      (((~ (v1_funct_1 @ sk_B) | ~ (v1_relat_1 @ sk_B)))
% 0.45/0.70         <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.70  thf('73', plain,
% 0.45/0.70      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_relat_1 @ sk_B)))
% 0.45/0.70         <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['55', '72'])).
% 0.45/0.70  thf('74', plain,
% 0.45/0.70      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.70  thf('76', plain, (((v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup+', [status(thm)], ['74', '75'])).
% 0.45/0.70  thf('77', plain, ((~ (v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('demod', [status(thm)], ['73', '76'])).
% 0.45/0.70  thf('78', plain, ((~ (v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['54', '77'])).
% 0.45/0.70  thf('79', plain, (((v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.45/0.70      inference('sup+', [status(thm)], ['74', '75'])).
% 0.45/0.70  thf('80', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.70  thf('81', plain, (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 0.45/0.70      inference('split', [status(esa)], ['52'])).
% 0.45/0.70  thf('82', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.45/0.70      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 0.45/0.70  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.70      inference('simpl_trail', [status(thm)], ['53', '82'])).
% 0.45/0.70  thf('84', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X0)) | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X1))),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['51', '83'])).
% 0.45/0.70  thf('85', plain,
% 0.45/0.70      (![X9 : $i, X11 : $i]:
% 0.45/0.70         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.70  thf('86', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X1))
% 0.45/0.70          | (r1_tarski @ (k1_tarski @ (sk_C_2 @ X1 @ sk_A)) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.70  thf('87', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.70          | (r2_hidden @ X0 @ X2)
% 0.45/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.70  thf('88', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X1))
% 0.45/0.70          | (r2_hidden @ X2 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X2 @ (k1_tarski @ (sk_C_2 @ X1 @ sk_A))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.70  thf('89', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.45/0.70          | (r2_hidden @ (sk_C_1 @ X1 @ k1_xboole_0) @ X2)
% 0.45/0.70          | ((sk_A) = (k1_tarski @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['18', '88'])).
% 0.45/0.70  thf('90', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X0)) | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X1))),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['51', '83'])).
% 0.45/0.70  thf('91', plain,
% 0.45/0.70      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X6 @ X4)
% 0.45/0.70          | ~ (r2_hidden @ X6 @ X7)
% 0.45/0.70          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.70  thf('92', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X1))
% 0.45/0.70          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.70          | ~ (r2_hidden @ (sk_C_2 @ X1 @ sk_A) @ X2))),
% 0.45/0.70      inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.70  thf('93', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X0)) | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X1))),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['51', '83'])).
% 0.45/0.70  thf('94', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r1_xboole_0 @ X0 @ X2) | ((sk_A) = (k1_tarski @ X1)))),
% 0.45/0.70      inference('clc', [status(thm)], ['92', '93'])).
% 0.45/0.70  thf('95', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (((sk_A) = (k1_tarski @ X0))
% 0.45/0.70          | (r2_hidden @ (sk_C_1 @ X1 @ k1_xboole_0) @ X2))),
% 0.45/0.70      inference('clc', [status(thm)], ['89', '94'])).
% 0.45/0.70  thf('96', plain,
% 0.45/0.70      (![X1 : $i, X3 : $i]:
% 0.45/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.70  thf('97', plain,
% 0.45/0.70      (![X1 : $i, X3 : $i]:
% 0.45/0.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.70  thf('98', plain,
% 0.45/0.70      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.70  thf('99', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.70      inference('simplify', [status(thm)], ['98'])).
% 0.45/0.70  thf('100', plain,
% 0.45/0.70      (![X9 : $i, X10 : $i]:
% 0.45/0.70         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 0.45/0.70      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.45/0.70  thf('101', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['99', '100'])).
% 0.45/0.70  thf('102', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((r2_hidden @ X0 @ sk_A)
% 0.45/0.70          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['95', '101'])).
% 0.45/0.70  thf('103', plain,
% 0.45/0.70      (![X0 : $i]: (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ sk_A)),
% 0.45/0.70      inference('eq_fact', [status(thm)], ['102'])).
% 0.45/0.70  thf('104', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.70  thf('105', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['103', '104'])).
% 0.45/0.70  thf('106', plain,
% 0.45/0.70      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X6 @ X4)
% 0.45/0.70          | ~ (r2_hidden @ X6 @ X7)
% 0.45/0.70          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.70  thf('107', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.70          | ~ (r2_hidden @ (sk_C_1 @ X1 @ k1_xboole_0) @ X2))),
% 0.45/0.70      inference('sup-', [status(thm)], ['105', '106'])).
% 0.45/0.70  thf('108', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['103', '104'])).
% 0.45/0.70  thf('109', plain, (![X0 : $i, X2 : $i]: ~ (r1_xboole_0 @ X0 @ X2)),
% 0.45/0.70      inference('demod', [status(thm)], ['107', '108'])).
% 0.45/0.70  thf('110', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_xboole_0))
% 0.45/0.70          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ X1 @ sk_A) @ X0))))),
% 0.45/0.70      inference('clc', [status(thm)], ['13', '109'])).
% 0.45/0.70  thf('111', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((sk_B) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['0', '110'])).
% 0.45/0.70  thf('112', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['111'])).
% 0.45/0.70  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.70  thf('114', plain, ($false),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
