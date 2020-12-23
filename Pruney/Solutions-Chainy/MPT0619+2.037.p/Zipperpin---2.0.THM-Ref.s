%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TBI4OPUngj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:25 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  212 (2324 expanded)
%              Number of leaves         :   24 ( 661 expanded)
%              Depth                    :   29
%              Number of atoms          : 1997 (26441 expanded)
%              Number of equality atoms :  252 (3204 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_2 @ X14 @ X15 )
        = ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X15 ) ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X5: $i] :
      ( ( X5
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ X5 @ X1 )
        = X1 )
      | ( r2_hidden @ ( sk_C @ X5 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ X0 @ X1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 )
      | ( k1_xboole_0
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C @ k1_xboole_0 @ X1 )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X1: $i,X5: $i] :
      ( ( X5
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ X5 @ X1 )
       != X1 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
       != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( sk_C @ k1_xboole_0 @ X1 )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( r2_hidden @ ( sk_D @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B_1 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B_1 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_1 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B_1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_B_1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B_1 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_2 @ X14 @ X15 )
       != ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_1 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ ( k2_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) @ ( k1_funct_1 @ sk_B_1 @ X1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) )
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) )
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) )
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ X1 ) ) @ sk_B_1 )
        = sk_A )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_relat_1 @ sk_B_1 ) ) ) ) @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_relat_1 @ sk_B_1 ) ) ) )
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('51',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( sk_B @ ( k1_relat_1 @ sk_B_1 ) )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( sk_B @ ( k1_relat_1 @ sk_B_1 ) )
      = sk_A )
    | ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k1_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_B @ ( k1_relat_1 @ sk_B_1 ) )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['55','66'])).

thf('68',plain,
    ( ( sk_B @ ( k1_relat_1 @ sk_B_1 ) )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['55','66'])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','67','68'])).

thf('70',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ( k1_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','65'])).

thf('72',plain,
    ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B_1 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_2 @ X0 @ sk_B_1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( sk_D @ k1_xboole_0 @ sk_B_1 )
      = sk_A )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_2 @ X14 @ X15 )
        = ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X15 ) ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('80',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('86',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('88',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('90',plain,(
    ! [X15: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( X19
       != ( k1_funct_1 @ X15 @ X20 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('91',plain,(
    ! [X15: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X20 ) @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('99',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_B_1 ) )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('101',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( X18
        = ( k1_funct_1 @ X15 @ ( sk_D_1 @ X18 @ X15 ) ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('104',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( X18
        = ( k1_funct_1 @ X15 @ ( sk_D_1 @ X18 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D_1 @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('107',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('108',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('109',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('115',plain,
    ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( sk_D_1 @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ sk_B_1 )
      = sk_A )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['106','115'])).

thf('117',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('118',plain,
    ( ( sk_D_1 @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','118','119','120'])).

thf('122',plain,
    ( ( sk_D @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['72','121'])).

thf('123',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_2 @ X14 @ X15 )
        = ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X15 ) ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('124',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
      = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
    | ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
      = ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','118','119','120'])).

thf('128',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
      = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
      = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
    | ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
      = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','118','119','120'])).

thf('134',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
    = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_2 @ X14 @ X15 )
       != ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('139',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( sk_C_2 @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) @ sk_B_1 )
    = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['131','134'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
     != ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('149',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( X18
        = ( k1_funct_1 @ X15 @ ( sk_D_1 @ X18 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('156',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('164',plain,
    ( ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('165',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['152','153','154','164','165'])).

thf('167',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('171',plain,
    ( ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','118','119','120'])).

thf('173',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
      = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
    | ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('177',plain,
    ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
    = ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_B_1 )
       != ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['168','177'])).

thf('179',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( ( sk_D @ k1_xboole_0 @ sk_B_1 )
      = sk_A ) ),
    inference(eq_res,[status(thm)],['178'])).

thf('180',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('181',plain,
    ( ( sk_D @ k1_xboole_0 @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['179','180'])).

thf('182',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('183',plain,
    ( ( ( sk_C_2 @ k1_xboole_0 @ sk_B_1 )
     != ( sk_C_2 @ k1_xboole_0 @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['145','146','147','181','182'])).

thf('184',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('186',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['184','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TBI4OPUngj
% 0.16/0.38  % Computer   : n024.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 09:30:21 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 240 iterations in 0.143s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.62  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.62  thf(d5_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.62               ( ?[D:$i]:
% 0.39/0.62                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.39/0.62                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.39/0.62          | ((sk_C_2 @ X14 @ X15) = (k1_funct_1 @ X15 @ (sk_D @ X14 @ X15)))
% 0.39/0.62          | ((X14) = (k2_relat_1 @ X15))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf(d1_tarski, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X1 : $i, X5 : $i]:
% 0.39/0.62         (((X5) = (k1_tarski @ X1))
% 0.39/0.62          | ((sk_C @ X5 @ X1) = (X1))
% 0.39/0.62          | (r2_hidden @ (sk_C @ X5 @ X1) @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf(l22_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.62       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.39/0.62          | ~ (r2_hidden @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((sk_C @ X0 @ X1) = (X1))
% 0.39/0.62          | ((X0) = (k1_tarski @ X1))
% 0.39/0.62          | ((k2_xboole_0 @ (k1_tarski @ (sk_C @ X0 @ X1)) @ X0) = (X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf(t49_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((X0) != (k1_xboole_0))
% 0.39/0.62          | ((X0) = (k1_tarski @ X1))
% 0.39/0.62          | ((sk_C @ X0 @ X1) = (X1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X1 : $i]:
% 0.39/0.62         (((sk_C @ k1_xboole_0 @ X1) = (X1))
% 0.39/0.62          | ((k1_xboole_0) = (k1_tarski @ X1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf('8', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.39/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.39/0.62          | ~ (r2_hidden @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.39/0.62           = (k1_tarski @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.62  thf('12', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.62  thf('13', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X1 : $i, X5 : $i]:
% 0.39/0.62         (((X5) = (k1_tarski @ X1))
% 0.39/0.62          | ((sk_C @ X5 @ X1) != (X1))
% 0.39/0.62          | ~ (r2_hidden @ (sk_C @ X5 @ X1) @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.62          | ((sk_C @ k1_xboole_0 @ X0) != (X0))
% 0.39/0.62          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.62  thf('16', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.62          | ((X0) != (X0))
% 0.39/0.62          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.62  thf('19', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.62  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 0.39/0.62          | ((sk_C_2 @ k1_xboole_0 @ X0)
% 0.39/0.62              = (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '20'])).
% 0.39/0.62  thf(t7_xboole_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.62  thf(t69_enumset1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.62  thf('23', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.39/0.62          | (r2_hidden @ (sk_D @ X14 @ X15) @ (k1_relat_1 @ X15))
% 0.39/0.62          | ((X14) = (k2_relat_1 @ X15))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf(t14_funct_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.62       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.62         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i]:
% 0.39/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.62          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.62            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.39/0.62  thf('25', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X1 : $i, X4 : $i]:
% 0.39/0.62         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)) | ((X0) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['25', '27'])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B_1) @ X0)
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '28'])).
% 0.39/0.62  thf('30', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B_1) @ X0)
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X1 : $i, X4 : $i]:
% 0.39/0.62         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_D @ (k1_tarski @ X0) @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B_1) = (X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_D @ (k2_tarski @ X0 @ X0) @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_B_1) = (X0))
% 0.39/0.62          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['23', '34'])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B_1) @ X0)
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         (~ (r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.39/0.62          | ((sk_C_2 @ X14 @ X15) != (k1_funct_1 @ X15 @ X16))
% 0.39/0.62          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.39/0.62          | ((X14) = (k2_relat_1 @ X15))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_C_2 @ X0 @ sk_B_1) != (k1_funct_1 @ sk_B_1 @ X1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.62  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_C_2 @ X0 @ sk_B_1) != (k1_funct_1 @ sk_B_1 @ X1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B_1) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.39/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.39/0.62          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ (k2_tarski @ X0 @ X0) @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((sk_D @ (k1_tarski @ X0) @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) @ sk_B_1)
% 0.39/0.62              = (sk_A))
% 0.39/0.62          | ((sk_D @ 
% 0.39/0.62              (k2_tarski @ (k1_funct_1 @ sk_B_1 @ X1) @ 
% 0.39/0.62               (k1_funct_1 @ sk_B_1 @ X1)) @ 
% 0.39/0.62              sk_B_1) = (sk_A))
% 0.39/0.62          | ((k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.39/0.62  thf('45', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) @ sk_B_1)
% 0.39/0.62              = (sk_A))
% 0.39/0.62          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) @ sk_B_1)
% 0.39/0.62              = (sk_A))
% 0.39/0.62          | ((k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X1 : $i]:
% 0.39/0.62         (((k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ X1)) @ sk_B_1)
% 0.39/0.62              = (sk_A))
% 0.39/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.39/0.62        | ((sk_D @ 
% 0.39/0.62            (k1_tarski @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_relat_1 @ sk_B_1)))) @ 
% 0.39/0.62            sk_B_1) = (sk_A))
% 0.39/0.62        | ((k1_tarski @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_relat_1 @ sk_B_1))))
% 0.39/0.62            = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['22', '47'])).
% 0.39/0.62  thf('49', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X1 : $i, X4 : $i]:
% 0.39/0.62         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      ((((sk_B @ (k1_relat_1 @ sk_B_1)) = (sk_A))
% 0.39/0.62        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['49', '52'])).
% 0.39/0.62  thf('54', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      ((((sk_B @ (k1_relat_1 @ sk_B_1)) = (sk_A))
% 0.39/0.62        | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.39/0.62  thf('56', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('57', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.39/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.39/0.62  thf('58', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.39/0.62          | ~ (r2_hidden @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62         = (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('61', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62         = (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['60', '61'])).
% 0.39/0.62  thf('63', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ X0) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('66', plain, (((k1_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['62', '65'])).
% 0.39/0.62  thf('67', plain, (((sk_B @ (k1_relat_1 @ sk_B_1)) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['55', '66'])).
% 0.39/0.62  thf('68', plain, (((sk_B @ (k1_relat_1 @ sk_B_1)) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['55', '66'])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.39/0.62        | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)) @ sk_B_1)
% 0.39/0.62            = (sk_A))
% 0.39/0.62        | ((k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['48', '67', '68'])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('71', plain, (((k1_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['62', '65'])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)) @ sk_B_1) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['69', '70', '71'])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | (r2_hidden @ (sk_C_2 @ X0 @ sk_B_1) @ X0)
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.39/0.62          | ~ (r2_hidden @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((k2_xboole_0 @ (k1_tarski @ (sk_C_2 @ X0 @ sk_B_1)) @ X0) = (X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((X0) != (k1_xboole_0))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      ((((sk_D @ k1_xboole_0 @ sk_B_1) = (sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['77'])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.39/0.62          | ((sk_C_2 @ X14 @ X15) = (k1_funct_1 @ X15 @ (sk_D @ X14 @ X15)))
% 0.39/0.62          | ((X14) = (k2_relat_1 @ X15))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['78', '79'])).
% 0.39/0.62  thf('81', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('82', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.39/0.62  thf('84', plain,
% 0.39/0.62      (((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ k1_xboole_0)
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['83'])).
% 0.39/0.62  thf('85', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.39/0.62          | ~ (r2_hidden @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.62  thf('86', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ((k2_xboole_0 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ 
% 0.39/0.62            k1_xboole_0) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.62  thf('88', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.39/0.62  thf('89', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.62  thf('90', plain,
% 0.39/0.62      (![X15 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.39/0.62         (((X17) != (k2_relat_1 @ X15))
% 0.39/0.62          | (r2_hidden @ X19 @ X17)
% 0.39/0.62          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 0.39/0.62          | ((X19) != (k1_funct_1 @ X15 @ X20))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('91', plain,
% 0.39/0.62      (![X15 : $i, X20 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X15)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 0.39/0.62          | (r2_hidden @ (k1_funct_1 @ X15 @ X20) @ (k2_relat_1 @ X15)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['90'])).
% 0.39/0.62  thf('92', plain,
% 0.39/0.62      (((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['89', '91'])).
% 0.39/0.62  thf('93', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('94', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('95', plain,
% 0.39/0.62      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.39/0.62  thf('96', plain,
% 0.39/0.62      (((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['88', '95'])).
% 0.39/0.62  thf('97', plain,
% 0.39/0.62      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.39/0.62  thf('98', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.39/0.62          | ~ (r2_hidden @ X8 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      (((k2_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)) @ 
% 0.39/0.62         (k2_relat_1 @ sk_B_1)) = (k2_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.62  thf('100', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.62  thf('101', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('102', plain,
% 0.39/0.62      ((r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['96', '101'])).
% 0.39/0.62  thf('103', plain,
% 0.39/0.62      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         (((X17) != (k2_relat_1 @ X15))
% 0.39/0.62          | ((X18) = (k1_funct_1 @ X15 @ (sk_D_1 @ X18 @ X15)))
% 0.39/0.62          | ~ (r2_hidden @ X18 @ X17)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('104', plain,
% 0.39/0.62      (![X15 : $i, X18 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X15)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.39/0.62          | ((X18) = (k1_funct_1 @ X15 @ (sk_D_1 @ X18 @ X15))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['103'])).
% 0.39/0.62  thf('105', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1)
% 0.39/0.62          = (k1_funct_1 @ sk_B_1 @ 
% 0.39/0.62             (sk_D_1 @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ sk_B_1)))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['102', '104'])).
% 0.39/0.62  thf('106', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.39/0.62  thf('107', plain,
% 0.39/0.62      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.39/0.62  thf('108', plain,
% 0.39/0.62      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         (((X17) != (k2_relat_1 @ X15))
% 0.39/0.62          | (r2_hidden @ (sk_D_1 @ X18 @ X15) @ (k1_relat_1 @ X15))
% 0.39/0.62          | ~ (r2_hidden @ X18 @ X17)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('109', plain,
% 0.39/0.62      (![X15 : $i, X18 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X15)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.39/0.62          | (r2_hidden @ (sk_D_1 @ X18 @ X15) @ (k1_relat_1 @ X15)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['108'])).
% 0.39/0.62  thf('110', plain,
% 0.39/0.62      (((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.39/0.62         (k1_relat_1 @ sk_B_1))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['107', '109'])).
% 0.39/0.62  thf('111', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('112', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('113', plain,
% 0.39/0.62      ((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.39/0.62        (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.39/0.62  thf('114', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)) | ((X0) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['25', '27'])).
% 0.39/0.62  thf('115', plain,
% 0.39/0.62      (((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['113', '114'])).
% 0.39/0.62  thf('116', plain,
% 0.39/0.62      ((((sk_D_1 @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ sk_B_1) = (sk_A))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['106', '115'])).
% 0.39/0.62  thf('117', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('118', plain,
% 0.39/0.62      (((sk_D_1 @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ sk_B_1) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 0.39/0.62  thf('119', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('120', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('121', plain,
% 0.39/0.62      (((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '118', '119', '120'])).
% 0.39/0.62  thf('122', plain,
% 0.39/0.62      (((sk_D @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62         = (sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['72', '121'])).
% 0.39/0.62  thf('123', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.39/0.62          | ((sk_C_2 @ X14 @ X15) = (k1_funct_1 @ X15 @ (sk_D @ X14 @ X15)))
% 0.39/0.62          | ((X14) = (k2_relat_1 @ X15))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('124', plain,
% 0.39/0.62      (![X1 : $i, X4 : $i]:
% 0.39/0.62         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('125', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X1)
% 0.39/0.62          | ~ (v1_funct_1 @ X1)
% 0.39/0.62          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ X0) @ X1)
% 0.39/0.62              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['123', '124'])).
% 0.39/0.62  thf('126', plain,
% 0.39/0.62      ((((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62          = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62            = (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62        | ((k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62            = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['122', '125'])).
% 0.39/0.62  thf('127', plain,
% 0.39/0.62      (((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '118', '119', '120'])).
% 0.39/0.62  thf('128', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('129', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('130', plain,
% 0.39/0.62      ((((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62          = (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62        | ((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62            = (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62        | ((k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62            = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.39/0.62  thf('131', plain,
% 0.39/0.62      ((((k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62            = (sk_C_2 @ k1_xboole_0 @ sk_B_1)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['130'])).
% 0.39/0.62  thf('132', plain,
% 0.39/0.62      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('133', plain,
% 0.39/0.62      (((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '118', '119', '120'])).
% 0.39/0.62  thf('134', plain,
% 0.39/0.62      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['132', '133'])).
% 0.39/0.62  thf('135', plain,
% 0.39/0.62      (((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62         = (sk_C_2 @ k1_xboole_0 @ sk_B_1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['131', '134'])).
% 0.39/0.62  thf('136', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         (~ (r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.39/0.62          | ((sk_C_2 @ X14 @ X15) != (k1_funct_1 @ X15 @ X16))
% 0.39/0.62          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.39/0.62          | ((X14) = (k2_relat_1 @ X15))
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('137', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ sk_B_1) @ 
% 0.39/0.62             (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)))
% 0.39/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62          | ((k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62              = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62              != (k1_funct_1 @ sk_B_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['135', '136'])).
% 0.39/0.62  thf('138', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.39/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.39/0.62  thf('139', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('140', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('141', plain,
% 0.39/0.62      (((sk_C_2 @ (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)) @ sk_B_1)
% 0.39/0.62         = (sk_C_2 @ k1_xboole_0 @ sk_B_1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['131', '134'])).
% 0.39/0.62  thf('142', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62            = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_C_2 @ k1_xboole_0 @ sk_B_1) != (k1_funct_1 @ sk_B_1 @ X0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.39/0.62  thf('143', plain,
% 0.39/0.62      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (sk_C_2 @ k1_xboole_0 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['132', '133'])).
% 0.39/0.62  thf('144', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_C_2 @ k1_xboole_0 @ sk_B_1) != (k1_funct_1 @ sk_B_1 @ X0)))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 0.39/0.62  thf('145', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) != (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62        | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B_1) @ (k1_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '144'])).
% 0.39/0.62  thf('146', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('147', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('148', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.62  thf('149', plain,
% 0.39/0.62      (![X15 : $i, X18 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X15)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.39/0.62          | ((X18) = (k1_funct_1 @ X15 @ (sk_D_1 @ X18 @ X15))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['103'])).
% 0.39/0.62  thf('150', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B @ (k2_relat_1 @ X0))
% 0.39/0.62              = (k1_funct_1 @ X0 @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ X0)) @ X0)))
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.62  thf('151', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B_1) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.39/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf('152', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B_1) != (sk_B @ (k2_relat_1 @ sk_B_1)))
% 0.39/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62          | ~ (r2_hidden @ 
% 0.39/0.62               (sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) @ 
% 0.39/0.62               (k1_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['150', '151'])).
% 0.39/0.62  thf('153', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('154', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('155', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.62  thf('156', plain,
% 0.39/0.62      (![X15 : $i, X18 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X15)
% 0.39/0.62          | ~ (v1_funct_1 @ X15)
% 0.39/0.62          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.39/0.62          | (r2_hidden @ (sk_D_1 @ X18 @ X15) @ (k1_relat_1 @ X15)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['108'])).
% 0.39/0.62  thf('157', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.39/0.62          | (r2_hidden @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.39/0.62             (k1_relat_1 @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['155', '156'])).
% 0.39/0.62  thf('158', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)) | ((X0) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['25', '27'])).
% 0.39/0.62  thf('159', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.39/0.62        | ((sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['157', '158'])).
% 0.39/0.62  thf('160', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('161', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('162', plain,
% 0.39/0.62      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.39/0.62        | ((sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.39/0.62  thf('163', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('164', plain,
% 0.39/0.62      (((sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 0.39/0.62  thf('165', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.62  thf('166', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B_1) != (sk_B @ (k2_relat_1 @ sk_B_1)))
% 0.39/0.62          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['152', '153', '154', '164', '165'])).
% 0.39/0.62  thf('167', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('168', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B_1) != (sk_B @ (k2_relat_1 @ sk_B_1)))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['166', '167'])).
% 0.39/0.62  thf('169', plain,
% 0.39/0.62      (((sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 0.39/0.62  thf('170', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.39/0.62          | ((sk_B @ (k2_relat_1 @ X0))
% 0.39/0.62              = (k1_funct_1 @ X0 @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ X0)) @ X0)))
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.62  thf('171', plain,
% 0.39/0.62      ((((sk_B @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_B_1)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.39/0.62        | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['169', '170'])).
% 0.39/0.62  thf('172', plain,
% 0.39/0.62      (((sk_C_2 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '118', '119', '120'])).
% 0.39/0.62  thf('173', plain, ((v1_relat_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('174', plain, ((v1_funct_1 @ sk_B_1)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('175', plain,
% 0.39/0.62      ((((sk_B @ (k2_relat_1 @ sk_B_1)) = (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62        | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 0.39/0.62  thf('176', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('177', plain,
% 0.39/0.62      (((sk_B @ (k2_relat_1 @ sk_B_1)) = (sk_C_2 @ k1_xboole_0 @ sk_B_1))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['175', '176'])).
% 0.39/0.62  thf('178', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((sk_C_2 @ X0 @ sk_B_1) != (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 0.39/0.62          | ((X0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['168', '177'])).
% 0.39/0.62  thf('179', plain,
% 0.39/0.62      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 0.39/0.62        | ((sk_D @ k1_xboole_0 @ sk_B_1) = (sk_A)))),
% 0.39/0.62      inference('eq_res', [status(thm)], ['178'])).
% 0.39/0.62  thf('180', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('181', plain, (((sk_D @ k1_xboole_0 @ sk_B_1) = (sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['179', '180'])).
% 0.39/0.62  thf('182', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.62  thf('183', plain,
% 0.39/0.62      ((((sk_C_2 @ k1_xboole_0 @ sk_B_1) != (sk_C_2 @ k1_xboole_0 @ sk_B_1))
% 0.39/0.62        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['145', '146', '147', '181', '182'])).
% 0.39/0.62  thf('184', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B_1))),
% 0.39/0.62      inference('simplify', [status(thm)], ['183'])).
% 0.39/0.62  thf('185', plain, (((k2_relat_1 @ sk_B_1) != (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('186', plain, ($false),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['184', '185'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
