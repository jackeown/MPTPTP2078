%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.34L4j5xwzG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 203 expanded)
%              Number of leaves         :   20 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  728 (3257 expanded)
%              Number of equality atoms :   23 ( 114 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(t38_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
        <=> ( ( A = B )
            | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
         => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
          <=> ( ( A = B )
              | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_wellord1])).

thf('0',plain,
    ( ( sk_A != sk_B_1 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_B_1 )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_2 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X8 ) @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C )
    | ~ ( v1_relat_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ~ ( v2_wellord1 @ X6 )
      | ( v1_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('8',plain,
    ( ( v1_relat_2 @ sk_C )
    | ~ ( v2_wellord1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_wellord1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_2 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ( r1_tarski @ ( k1_wellord1 @ X9 @ X10 ) @ ( k1_wellord1 @ X9 @ X11 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C ) )
      | ~ ( v2_wellord1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_wellord1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ( sk_A = sk_B_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_A ) )
   <= ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
      & ( sk_A = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A != sk_B_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X9 @ X10 ) @ ( k1_wellord1 @ X9 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C )
      | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
      | ~ ( v2_wellord1 @ sk_C ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_wellord1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

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

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( X5 = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
      | ( sk_A = sk_B_1 )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
      | ( sk_A = sk_B_1 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A != sk_B_1 )
   <= ( sk_A != sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ( sk_A != sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('43',plain,(
    sk_A != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['1','42'])).

thf('44',plain,(
    sk_A != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('51',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('56',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','25','27','47','48','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.34L4j5xwzG
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 77 iterations in 0.036s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.51  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.20/0.51  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.20/0.51  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.51  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.20/0.51  thf(t38_wellord1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.51           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.51         ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.20/0.51           ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ C ) =>
% 0.20/0.51          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.51              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.51            ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.20/0.51              ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t38_wellord1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((sk_A) != (sk_B_1))
% 0.20/0.51        | ~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51             (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (~ (((sk_A) = (sk_B_1))) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(l1_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( v1_relat_2 @ A ) <=>
% 0.20/0.51         ( ![B:$i]:
% 0.20/0.51           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.20/0.51             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (v1_relat_2 @ X7)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X8 @ X8) @ X7)
% 0.20/0.51          | ~ (r2_hidden @ X8 @ (k3_relat_1 @ X7))
% 0.20/0.51          | ~ (v1_relat_1 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C)
% 0.20/0.51        | ~ (v1_relat_2 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d4_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( v2_wellord1 @ A ) <=>
% 0.20/0.51         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.20/0.51           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X6 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X6) | (v1_relat_2 @ X6) | ~ (v1_relat_1 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.20/0.51  thf('8', plain, (((v1_relat_2 @ sk_C) | ~ (v2_wellord1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v2_wellord1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((v1_relat_2 @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_A) @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.20/0.51  thf('12', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t37_wellord1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.51           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.51         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X9)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X9))
% 0.20/0.51          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.20/0.51          | (r1_tarski @ (k1_wellord1 @ X9 @ X10) @ (k1_wellord1 @ X9 @ X11))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ sk_C)
% 0.20/0.51          | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51             (k1_wellord1 @ sk_C @ X0))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C))
% 0.20/0.51          | ~ (v2_wellord1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain, ((v2_wellord1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ X0))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))
% 0.20/0.51        | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51           (k1_wellord1 @ sk_C @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.51  thf('19', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))
% 0.20/0.51        | ((sk_A) = (sk_B_1))
% 0.20/0.51        | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51           (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51           (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51           (k1_wellord1 @ sk_C @ sk_A)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))) & 
% 0.20/0.51             (((sk_A) = (sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (~ (((sk_A) = (sk_B_1))) | 
% 0.20/0.51       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))
% 0.20/0.51        | ~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51             (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['21'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (v2_wellord1 @ X9)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X9))
% 0.20/0.51          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.20/0.51          | ~ (r1_tarski @ (k1_wellord1 @ X9 @ X10) @ (k1_wellord1 @ X9 @ X11))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.51         | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C)
% 0.20/0.51         | ~ (r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C))
% 0.20/0.51         | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))
% 0.20/0.51         | ~ (v2_wellord1 @ sk_C)))
% 0.20/0.51         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((v2_wellord1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C))
% 0.20/0.51         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.20/0.51  thf(d1_wellord1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.51         (((X3) != (k1_wellord1 @ X2 @ X1))
% 0.20/0.51          | (r2_hidden @ X5 @ X3)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.20/0.51          | ((X5) = (X1))
% 0.20/0.51          | ~ (v1_relat_1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X2)
% 0.20/0.51          | ((X5) = (X1))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.20/0.51          | (r2_hidden @ X5 @ (k1_wellord1 @ X2 @ X1)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))
% 0.20/0.51         | ((sk_A) = (sk_B_1))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.51         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.51  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))
% 0.20/0.51         | ((sk_A) = (sk_B_1))))
% 0.20/0.51         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((((sk_A) != (sk_B_1))) <= (~ (((sk_A) = (sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1))) | 
% 0.20/0.51       ~ (((sk_A) = (sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '24'])).
% 0.20/0.51  thf('43', plain, (~ (((sk_A) = (sk_B_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '42'])).
% 0.20/0.51  thf('44', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['40', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['26'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))) | 
% 0.20/0.51       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1))) | 
% 0.20/0.51       (((sk_A) = (sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['21'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['21'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (((X3) != (k1_wellord1 @ X2 @ X1))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X4 @ X1) @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ X3)
% 0.20/0.51          | ~ (v1_relat_1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ (k1_wellord1 @ X2 @ X1))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X4 @ X1) @ X2))),
% 0.20/0.51      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C)
% 0.20/0.51         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '51'])).
% 0.20/0.51  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ X0))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((~ (r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C))
% 0.20/0.51         | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51            (k1_wellord1 @ sk_C @ sk_B_1))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51           (k1_wellord1 @ sk_C @ sk_B_1)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51               (k1_wellord1 @ sk_C @ sk_B_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B_1))) | 
% 0.20/0.51       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.51         (k1_wellord1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('61', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)],
% 0.20/0.51                ['1', '25', '27', '47', '48', '60'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
