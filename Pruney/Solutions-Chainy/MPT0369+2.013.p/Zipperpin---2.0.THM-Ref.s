%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1zZv2ZL2nl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:16 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 348 expanded)
%              Number of leaves         :   23 ( 112 expanded)
%              Depth                    :   15
%              Number of atoms          :  558 (2949 expanded)
%              Number of equality atoms :   30 ( 143 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C_2 @ X0 )
      | ( r2_hidden @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C_2 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_2 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_C_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['11','25'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_xboole_0 @ ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['26','50'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['8','57'])).

thf('59',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( X0 = sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    k1_xboole_0 = sk_C_2 ),
    inference('sup-',[status(thm)],['7','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('65',plain,
    ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    = sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['26','50'])).

thf('68',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1zZv2ZL2nl
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 165 iterations in 0.144s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(t4_subset_1, axiom,
% 0.41/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.60  thf(d2_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.60         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.60       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X23 @ X24)
% 0.41/0.60          | (r2_hidden @ X23 @ X24)
% 0.41/0.60          | (v1_xboole_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.41/0.60          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf(fc1_subset_1, axiom,
% 0.41/0.60    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.60  thf('3', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.60  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.60      inference('clc', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf(d1_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X21 @ X20)
% 0.41/0.60          | (r1_tarski @ X21 @ X19)
% 0.41/0.60          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X19 : $i, X21 : $i]:
% 0.41/0.60         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.60  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '6'])).
% 0.41/0.60  thf(d3_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i]:
% 0.41/0.60         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf(t50_subset_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ A ) =>
% 0.41/0.60               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.41/0.60                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( m1_subset_1 @ C @ A ) =>
% 0.41/0.60                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.41/0.60                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.41/0.60  thf('9', plain, ((m1_subset_1 @ sk_C_2 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X25 @ X24)
% 0.41/0.60          | (v1_xboole_0 @ X25)
% 0.41/0.60          | ~ (v1_xboole_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.60  thf('11', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d5_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.41/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain, ((m1_subset_1 @ sk_C_2 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X23 @ X24)
% 0.41/0.60          | (r2_hidden @ X23 @ X24)
% 0.41/0.60          | (v1_xboole_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.60  thf('17', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_2 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf(d5_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.41/0.60       ( ![D:$i]:
% 0.41/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X7 @ X8)
% 0.41/0.60          | (r2_hidden @ X7 @ X9)
% 0.41/0.60          | (r2_hidden @ X7 @ X10)
% 0.41/0.60          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         ((r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.41/0.60          | (r2_hidden @ X7 @ X9)
% 0.41/0.60          | ~ (r2_hidden @ X7 @ X8))),
% 0.41/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_A)
% 0.41/0.60          | (r2_hidden @ sk_C_2 @ X0)
% 0.41/0.60          | (r2_hidden @ sk_C_2 @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['17', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (((r2_hidden @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.41/0.60        | (r2_hidden @ sk_C_2 @ sk_B_1)
% 0.41/0.60        | (v1_xboole_0 @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['14', '20'])).
% 0.41/0.60  thf('22', plain, (~ (r2_hidden @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('23', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_2 @ sk_B_1))),
% 0.41/0.60      inference('clc', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, (~ (r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('25', plain, ((v1_xboole_0 @ sk_A)),
% 0.41/0.60      inference('clc', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('26', plain, ((v1_xboole_0 @ sk_C_2)),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '25'])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i]:
% 0.41/0.60         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.41/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.60          | (r2_hidden @ X11 @ X8)
% 0.41/0.60          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.60         ((r2_hidden @ X11 @ X8)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.41/0.60          | (r2_hidden @ X1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.41/0.60          | (r2_hidden @ (sk_B @ (k3_subset_1 @ X0 @ k1_xboole_0)) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['27', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ X9)
% 0.41/0.60          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X9)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.41/0.60          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '38'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.41/0.60          | ~ (r2_hidden @ (sk_B @ (k3_subset_1 @ X0 @ k1_xboole_0)) @ 
% 0.41/0.60               k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '39'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (((v1_xboole_0 @ (k3_subset_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.41/0.60        | (v1_xboole_0 @ (k3_subset_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['34', '40'])).
% 0.41/0.60  thf('42', plain, ((v1_xboole_0 @ (k3_subset_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['41'])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i]:
% 0.41/0.60         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X13 : $i, X15 : $i]:
% 0.41/0.60         (((X13) = (X15))
% 0.41/0.60          | ~ (r1_tarski @ X15 @ X13)
% 0.41/0.60          | ~ (r1_tarski @ X13 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['45', '48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '49'])).
% 0.41/0.60  thf('51', plain, (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (sk_C_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '50'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.41/0.60          | (r2_hidden @ X1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '32'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ sk_C_2) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.41/0.60  thf('54', plain, (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (sk_C_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '50'])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.41/0.60          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '38'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.60  thf('57', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_2)),
% 0.41/0.60      inference('clc', [status(thm)], ['53', '56'])).
% 0.41/0.60  thf('58', plain, (![X0 : $i]: (r1_tarski @ sk_C_2 @ X0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '57'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (![X13 : $i, X15 : $i]:
% 0.41/0.60         (((X13) = (X15))
% 0.41/0.60          | ~ (r1_tarski @ X15 @ X13)
% 0.41/0.60          | ~ (r1_tarski @ X13 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_2) | ((X0) = (sk_C_2)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.60  thf('61', plain, (((k1_xboole_0) = (sk_C_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '60'])).
% 0.41/0.60  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('63', plain, ((v1_xboole_0 @ sk_A)),
% 0.41/0.60      inference('clc', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '49'])).
% 0.41/0.60  thf('65', plain, (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['62', '65'])).
% 0.41/0.60  thf('67', plain, (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (sk_C_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '50'])).
% 0.41/0.60  thf('68', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['66', '67'])).
% 0.41/0.60  thf('69', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['61', '68'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
