%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9kWi6wZ3tY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 172 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  429 (1779 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(t54_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( v2_wellord1 @ A )
                  & ( r3_wellord1 @ A @ B @ C ) )
               => ( v2_wellord1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( v2_wellord1 @ A )
                    & ( r3_wellord1 @ A @ B @ C ) )
                 => ( v2_wellord1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_wellord1])).

thf('0',plain,(
    v1_relat_1 @ sk_B ),
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

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('2',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v1_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t53_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ( ( ( v1_relat_2 @ A )
                   => ( v1_relat_2 @ B ) )
                  & ( ( v8_relat_2 @ A )
                   => ( v8_relat_2 @ B ) )
                  & ( ( v6_relat_2 @ A )
                   => ( v6_relat_2 @ B ) )
                  & ( ( v4_relat_2 @ A )
                   => ( v4_relat_2 @ B ) )
                  & ( ( v1_wellord1 @ A )
                   => ( v1_wellord1 @ B ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_wellord1 @ X2 )
      | ( v1_wellord1 @ X1 )
      | ~ ( r3_wellord1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_wellord1 @ sk_B )
    | ~ ( v1_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('11',plain,
    ( ( v1_wellord1 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_wellord1 @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_wellord1 @ sk_B ),
    inference(demod,[status(thm)],['5','6','7','8','13','14'])).

thf('16',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['2','15'])).

thf('17',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v4_relat_2 @ X2 )
      | ( v4_relat_2 @ X1 )
      | ~ ( r3_wellord1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v4_relat_2 @ sk_B )
    | ~ ( v4_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v4_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('25',plain,
    ( ( v4_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['19','20','21','22','27','28'])).

thf('30',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v6_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['16','29'])).

thf('31',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v6_relat_2 @ X2 )
      | ( v6_relat_2 @ X1 )
      | ~ ( r3_wellord1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v6_relat_2 @ sk_B )
    | ~ ( v6_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v6_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('39',plain,
    ( ( v6_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v6_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v6_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['33','34','35','36','41','42'])).

thf('44',plain,
    ( ( v2_wellord1 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['30','43'])).

thf('45',plain,(
    ~ ( v2_wellord1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v8_relat_2 @ X2 )
      | ( v8_relat_2 @ X1 )
      | ~ ( r3_wellord1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v8_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v8_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('55',plain,
    ( ( v8_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v8_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v8_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['49','50','51','52','57','58'])).

thf('60',plain,(
    ~ ( v1_relat_2 @ sk_B ) ),
    inference(demod,[status(thm)],['46','59'])).

thf('61',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_2 @ X2 )
      | ( v1_relat_2 @ X1 )
      | ~ ( r3_wellord1 @ X2 @ X1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t53_wellord1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_relat_2 @ sk_B )
    | ~ ( v1_relat_2 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('69',plain,
    ( ( v1_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_2 @ sk_B ),
    inference(demod,[status(thm)],['63','64','65','66','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['60','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9kWi6wZ3tY
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 43 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.21/0.47  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.21/0.47  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.21/0.47  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.21/0.47  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.21/0.47  thf(t54_wellord1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48               ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.21/0.48                 ( v2_wellord1 @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( v1_relat_1 @ B ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48                  ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.21/0.48                    ( v2_wellord1 @ B ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t54_wellord1])).
% 0.21/0.48  thf('0', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d4_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( v2_wellord1 @ A ) <=>
% 0.21/0.48         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.21/0.48           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_2 @ X0)
% 0.21/0.48          | ~ (v8_relat_2 @ X0)
% 0.21/0.48          | ~ (v4_relat_2 @ X0)
% 0.21/0.48          | ~ (v6_relat_2 @ X0)
% 0.21/0.48          | ~ (v1_wellord1 @ X0)
% 0.21/0.48          | (v2_wellord1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((v2_wellord1 @ sk_B)
% 0.21/0.48        | ~ (v1_wellord1 @ sk_B)
% 0.21/0.48        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v4_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t53_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.21/0.48                 ( ( ( v1_relat_2 @ A ) => ( v1_relat_2 @ B ) ) & 
% 0.21/0.48                   ( ( v8_relat_2 @ A ) => ( v8_relat_2 @ B ) ) & 
% 0.21/0.48                   ( ( v6_relat_2 @ A ) => ( v6_relat_2 @ B ) ) & 
% 0.21/0.48                   ( ( v4_relat_2 @ A ) => ( v4_relat_2 @ B ) ) & 
% 0.21/0.48                   ( ( v1_wellord1 @ A ) => ( v1_wellord1 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_wellord1 @ X2)
% 0.21/0.48          | (v1_wellord1 @ X1)
% 0.21/0.48          | ~ (r3_wellord1 @ X2 @ X1 @ X3)
% 0.21/0.48          | ~ (v1_funct_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.48        | (v1_wellord1 @ sk_B)
% 0.21/0.48        | ~ (v1_wellord1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_wellord1 @ X0) | (v1_wellord1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.48  thf('11', plain, (((v1_wellord1 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, ((v1_wellord1 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, ((v1_wellord1 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '6', '7', '8', '13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((v2_wellord1 @ sk_B)
% 0.21/0.48        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v4_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '15'])).
% 0.21/0.48  thf('17', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v4_relat_2 @ X2)
% 0.21/0.48          | (v4_relat_2 @ X1)
% 0.21/0.48          | ~ (r3_wellord1 @ X2 @ X1 @ X3)
% 0.21/0.48          | ~ (v1_funct_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.48        | (v4_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v4_relat_2 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_wellord1 @ X0) | (v4_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.48  thf('25', plain, (((v4_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain, ((v4_relat_2 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, ((v4_relat_2 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21', '22', '27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (((v2_wellord1 @ sk_B)
% 0.21/0.48        | ~ (v6_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v8_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '29'])).
% 0.21/0.48  thf('31', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v6_relat_2 @ X2)
% 0.21/0.48          | (v6_relat_2 @ X1)
% 0.21/0.48          | ~ (r3_wellord1 @ X2 @ X1 @ X3)
% 0.21/0.48          | ~ (v1_funct_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.48        | (v6_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v6_relat_2 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_wellord1 @ X0) | (v6_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.48  thf('39', plain, (((v6_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain, ((v6_relat_2 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.48  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, ((v6_relat_2 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34', '35', '36', '41', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((v2_wellord1 @ sk_B) | ~ (v8_relat_2 @ sk_B) | ~ (v1_relat_2 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '43'])).
% 0.21/0.48  thf('45', plain, (~ (v2_wellord1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('46', plain, ((~ (v1_relat_2 @ sk_B) | ~ (v8_relat_2 @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v8_relat_2 @ X2)
% 0.21/0.48          | (v8_relat_2 @ X1)
% 0.21/0.48          | ~ (r3_wellord1 @ X2 @ X1 @ X3)
% 0.21/0.48          | ~ (v1_funct_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.48        | (v8_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v8_relat_2 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_wellord1 @ X0) | (v8_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.48  thf('55', plain, (((v8_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('57', plain, ((v8_relat_2 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('59', plain, ((v8_relat_2 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50', '51', '52', '57', '58'])).
% 0.21/0.48  thf('60', plain, (~ (v1_relat_2 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['46', '59'])).
% 0.21/0.48  thf('61', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_2 @ X2)
% 0.21/0.48          | (v1_relat_2 @ X1)
% 0.21/0.48          | ~ (r3_wellord1 @ X2 @ X1 @ X3)
% 0.21/0.48          | ~ (v1_funct_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X3)
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t53_wellord1])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.48        | (v1_relat_2 @ sk_B)
% 0.21/0.48        | ~ (v1_relat_2 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.48  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('67', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_wellord1 @ X0) | (v1_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.21/0.48  thf('69', plain, (((v1_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.48  thf('70', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('71', plain, ((v1_relat_2 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.48  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('73', plain, ((v1_relat_2 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['63', '64', '65', '66', '71', '72'])).
% 0.21/0.48  thf('74', plain, ($false), inference('demod', [status(thm)], ['60', '73'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
