%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ARYxkQRE3X

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:00 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 147 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  670 (1675 expanded)
%              Number of equality atoms :   52 ( 133 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ ( k11_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ X17 )
      | ( X17
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k11_relat_1 @ X20 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C_1 @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( sk_C_1 @ X18 @ X17 )
       != X18 )
      | ( X17
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X1 @ X0 )
       != X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('44',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('52',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['23','38','39','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ARYxkQRE3X
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 19:23:03 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.35/1.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.55  % Solved by: fo/fo7.sh
% 1.35/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.55  % done 1767 iterations in 1.095s
% 1.35/1.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.55  % SZS output start Refutation
% 1.35/1.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.35/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.35/1.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.35/1.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.35/1.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.35/1.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.35/1.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.55  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.35/1.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.55  thf(t117_funct_1, conjecture,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.35/1.55         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.35/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.55    (~( ![A:$i,B:$i]:
% 1.35/1.55        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.55          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.35/1.55            ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 1.35/1.55    inference('cnf.neg', [status(esa)], [t117_funct_1])).
% 1.35/1.55  thf('0', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf(t8_funct_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.35/1.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.35/1.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.35/1.55           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.35/1.55  thf('1', plain,
% 1.35/1.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 1.35/1.55          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 1.35/1.55          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 1.35/1.55          | ~ (v1_funct_1 @ X23)
% 1.35/1.55          | ~ (v1_relat_1 @ X23))),
% 1.35/1.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.35/1.55  thf('2', plain,
% 1.35/1.55      (![X22 : $i, X23 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X23)
% 1.35/1.55          | ~ (v1_funct_1 @ X23)
% 1.35/1.55          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 1.35/1.55          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 1.35/1.55      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.55  thf('3', plain,
% 1.35/1.55      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 1.35/1.55        | ~ (v1_funct_1 @ sk_B)
% 1.35/1.55        | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.55      inference('sup-', [status(thm)], ['0', '2'])).
% 1.35/1.55  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('6', plain,
% 1.35/1.55      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 1.35/1.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.35/1.55  thf(t204_relat_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ C ) =>
% 1.35/1.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.35/1.55         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 1.35/1.55  thf('7', plain,
% 1.35/1.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.55         (~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X20)
% 1.35/1.55          | (r2_hidden @ X19 @ (k11_relat_1 @ X20 @ X21))
% 1.35/1.55          | ~ (v1_relat_1 @ X20))),
% 1.35/1.55      inference('cnf', [status(esa)], [t204_relat_1])).
% 1.35/1.55  thf('8', plain,
% 1.35/1.55      ((~ (v1_relat_1 @ sk_B)
% 1.35/1.55        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('10', plain,
% 1.35/1.55      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 1.35/1.55      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.55  thf(d4_xboole_0, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.35/1.55       ( ![D:$i]:
% 1.35/1.55         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.35/1.55  thf('11', plain,
% 1.35/1.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.35/1.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.35/1.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.35/1.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.35/1.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.35/1.55  thf('12', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.35/1.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.55      inference('eq_fact', [status(thm)], ['11'])).
% 1.35/1.55  thf('13', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.35/1.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.55      inference('eq_fact', [status(thm)], ['11'])).
% 1.35/1.55  thf('14', plain,
% 1.35/1.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.35/1.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.35/1.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.35/1.55  thf('15', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.35/1.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['13', '14'])).
% 1.35/1.55  thf('16', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.35/1.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.55      inference('simplify', [status(thm)], ['15'])).
% 1.35/1.55  thf('17', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.35/1.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.55      inference('eq_fact', [status(thm)], ['11'])).
% 1.35/1.55  thf('18', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.35/1.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.35/1.55      inference('clc', [status(thm)], ['16', '17'])).
% 1.35/1.55  thf('19', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['12', '18'])).
% 1.35/1.55  thf('20', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['19'])).
% 1.35/1.55  thf(t4_xboole_0, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.35/1.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.35/1.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.35/1.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.35/1.55  thf('21', plain,
% 1.35/1.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 1.35/1.55          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.35/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.35/1.55  thf('22', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['20', '21'])).
% 1.35/1.55  thf('23', plain,
% 1.35/1.55      (~ (r1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A) @ 
% 1.35/1.55          (k11_relat_1 @ sk_B @ sk_A))),
% 1.35/1.55      inference('sup-', [status(thm)], ['10', '22'])).
% 1.35/1.55  thf(l44_zfmisc_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.35/1.55          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 1.35/1.55  thf('24', plain,
% 1.35/1.55      (![X17 : $i, X18 : $i]:
% 1.35/1.55         (((X17) = (k1_xboole_0))
% 1.35/1.55          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ X17)
% 1.35/1.55          | ((X17) = (k1_tarski @ X18)))),
% 1.35/1.55      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.35/1.55  thf('25', plain,
% 1.35/1.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X19 @ (k11_relat_1 @ X20 @ X21))
% 1.35/1.55          | (r2_hidden @ (k4_tarski @ X21 @ X19) @ X20)
% 1.35/1.55          | ~ (v1_relat_1 @ X20))),
% 1.35/1.55      inference('cnf', [status(esa)], [t204_relat_1])).
% 1.35/1.55  thf('26', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.55         (((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | (r2_hidden @ 
% 1.35/1.55             (k4_tarski @ X0 @ (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 1.35/1.55      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.55  thf('27', plain,
% 1.35/1.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.55         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 1.35/1.55          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 1.35/1.55          | ~ (v1_funct_1 @ X23)
% 1.35/1.55          | ~ (v1_relat_1 @ X23))),
% 1.35/1.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.35/1.55  thf('28', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X0)
% 1.35/1.55          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.35/1.55          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ X2))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ((sk_C_1 @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['26', '27'])).
% 1.35/1.55  thf('29', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.55         (((sk_C_1 @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1))
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ X2))
% 1.35/1.55          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.35/1.55          | ~ (v1_relat_1 @ X0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['28'])).
% 1.35/1.55  thf('30', plain,
% 1.35/1.55      (![X17 : $i, X18 : $i]:
% 1.35/1.55         (((X17) = (k1_xboole_0))
% 1.35/1.55          | ((sk_C_1 @ X18 @ X17) != (X18))
% 1.35/1.55          | ((X17) = (k1_tarski @ X18)))),
% 1.35/1.55      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.35/1.55  thf('31', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.55         (((k1_funct_1 @ X1 @ X0) != (X2))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.35/1.55          | ~ (v1_funct_1 @ X1)
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['29', '30'])).
% 1.35/1.55  thf('32', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_funct_1 @ X1)
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 1.35/1.55          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.35/1.55          | ~ (v1_relat_1 @ X1))),
% 1.35/1.55      inference('simplify', [status(thm)], ['31'])).
% 1.35/1.55  thf('33', plain,
% 1.35/1.55      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('34', plain,
% 1.35/1.55      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 1.35/1.55        | ~ (v1_relat_1 @ sk_B)
% 1.35/1.55        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.35/1.55        | ~ (v1_funct_1 @ sk_B))),
% 1.35/1.55      inference('sup-', [status(thm)], ['32', '33'])).
% 1.35/1.55  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('37', plain,
% 1.35/1.55      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 1.35/1.55        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.35/1.55      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.35/1.55  thf('38', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['37'])).
% 1.35/1.55  thf('39', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['37'])).
% 1.35/1.55  thf('40', plain,
% 1.35/1.55      (![X6 : $i, X7 : $i]:
% 1.35/1.55         ((r1_xboole_0 @ X6 @ X7)
% 1.35/1.55          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 1.35/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.35/1.55  thf('41', plain,
% 1.35/1.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X4 @ X3)
% 1.35/1.55          | (r2_hidden @ X4 @ X1)
% 1.35/1.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.35/1.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.35/1.55  thf('42', plain,
% 1.35/1.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.35/1.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.35/1.55      inference('simplify', [status(thm)], ['41'])).
% 1.35/1.55  thf('43', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 1.35/1.55      inference('sup-', [status(thm)], ['40', '42'])).
% 1.35/1.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.35/1.55  thf('44', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 1.35/1.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.35/1.55  thf('45', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.35/1.55          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.55      inference('eq_fact', [status(thm)], ['11'])).
% 1.35/1.55  thf('46', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['20', '21'])).
% 1.35/1.55  thf('47', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((X0) = (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['45', '46'])).
% 1.35/1.55  thf('48', plain,
% 1.35/1.55      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['44', '47'])).
% 1.35/1.55  thf('49', plain,
% 1.35/1.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 1.35/1.55          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.35/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.35/1.55  thf('50', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['48', '49'])).
% 1.35/1.55  thf('51', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 1.35/1.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.35/1.55  thf('52', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.35/1.55      inference('demod', [status(thm)], ['50', '51'])).
% 1.35/1.55  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.35/1.55      inference('sup-', [status(thm)], ['43', '52'])).
% 1.35/1.55  thf('54', plain, ($false),
% 1.35/1.55      inference('demod', [status(thm)], ['23', '38', '39', '53'])).
% 1.35/1.55  
% 1.35/1.55  % SZS output end Refutation
% 1.35/1.55  
% 1.35/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
