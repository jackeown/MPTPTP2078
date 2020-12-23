%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OgFueb9oKo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 148 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  617 (1121 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('5',plain,(
    ! [X21: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X21 ) @ ( k3_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['6','7','12'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( r1_ordinal1 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ X32 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( r1_ordinal1 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ X32 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('20',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( r2_hidden @ X27 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k1_ordinal1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('25',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( r1_ordinal1 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ X32 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ ( k1_ordinal1 @ X28 ) )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('53',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_ordinal1 @ X29 )
      | ( r2_hidden @ X30 @ X29 )
      | ( X30 = X29 )
      | ( r2_hidden @ X29 @ X30 )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('58',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('69',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('70',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OgFueb9oKo
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:57:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 175 iterations in 0.068s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.52  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.52  thf(t34_ordinal1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.52           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.52             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.52              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.52                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.52        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('2', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(t11_setfam_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.52  thf('3', plain, (![X20 : $i]: ((k1_setfam_1 @ (k1_tarski @ X20)) = (X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.20/0.52  thf('4', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t3_setfam_1, axiom,
% 0.20/0.52    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X21 : $i]: (r1_tarski @ (k1_setfam_1 @ X21) @ (k3_tarski @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('8', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(t31_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.52  thf('9', plain, (![X19 : $i]: ((k3_tarski @ (k1_tarski @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.52  thf('10', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7', '12'])).
% 0.20/0.52  thf(t26_ordinal1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.52           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X31 : $i, X32 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X31)
% 0.20/0.52          | (r1_ordinal1 @ X32 @ X31)
% 0.20/0.52          | (r2_hidden @ X31 @ X32)
% 0.20/0.52          | ~ (v3_ordinal1 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.52  thf(t7_ordinal1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X0)
% 0.20/0.52          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.52          | ~ (v3_ordinal1 @ X1)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X31 : $i, X32 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X31)
% 0.20/0.52          | (r1_ordinal1 @ X32 @ X31)
% 0.20/0.52          | (r2_hidden @ X31 @ X32)
% 0.20/0.52          | ~ (v3_ordinal1 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['20'])).
% 0.20/0.52  thf(t13_ordinal1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.52       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         (((X27) = (X26))
% 0.20/0.52          | (r2_hidden @ X27 @ X26)
% 0.20/0.52          | ~ (r2_hidden @ X27 @ (k1_ordinal1 @ X26)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.52         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.52         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.52  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.52         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((sk_A) = (sk_B)))
% 0.20/0.52         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.52             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.20/0.52         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.52             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((~ (v3_ordinal1 @ sk_A))
% 0.20/0.52         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.52             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '33'])).
% 0.20/0.52  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.52       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['20'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X31 : $i, X32 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X31)
% 0.20/0.52          | (r1_ordinal1 @ X32 @ X31)
% 0.20/0.52          | (r2_hidden @ X31 @ X32)
% 0.20/0.52          | ~ (v3_ordinal1 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i]:
% 0.20/0.52         ((r2_hidden @ X27 @ (k1_ordinal1 @ X28)) | ~ (r2_hidden @ X27 @ X28))),
% 0.20/0.52      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X0)
% 0.20/0.52          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.52          | ~ (v3_ordinal1 @ X1)
% 0.20/0.52          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.52         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_B)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.52  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.52       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X23)
% 0.20/0.52          | ~ (v3_ordinal1 @ X24)
% 0.20/0.52          | (r1_tarski @ X23 @ X24)
% 0.20/0.52          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((((r1_tarski @ sk_B @ sk_A)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_B)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ sk_A))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['20'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X23)
% 0.20/0.52          | ~ (v3_ordinal1 @ X24)
% 0.20/0.52          | (r1_tarski @ X23 @ X24)
% 0.20/0.52          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.52  thf(t24_ordinal1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.52           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.52                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X29 : $i, X30 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X29)
% 0.20/0.52          | (r2_hidden @ X30 @ X29)
% 0.20/0.52          | ((X30) = (X29))
% 0.20/0.52          | (r2_hidden @ X29 @ X30)
% 0.20/0.52          | ~ (v3_ordinal1 @ X30))),
% 0.20/0.52      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v3_ordinal1 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ((X1) = (X0))
% 0.20/0.52          | ~ (v3_ordinal1 @ X0)
% 0.20/0.52          | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.52         | ((sk_B) = (sk_A))
% 0.20/0.52         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.52         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '59'])).
% 0.20/0.52  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.20/0.52         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.20/0.52         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      ((((sk_B) = (sk_A)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.52             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '65'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.52             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.52  thf('69', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_ordinal1 @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.52       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.52  thf('71', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '70'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
