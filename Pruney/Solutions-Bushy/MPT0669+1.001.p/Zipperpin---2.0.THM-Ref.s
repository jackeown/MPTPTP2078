%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0669+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9YMjzINzxN

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 316 expanded)
%              Number of leaves         :   20 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  741 (4270 expanded)
%              Number of equality atoms :    6 (  17 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t86_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
        <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_funct_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t85_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
        & ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X9 @ X8 ) @ X11 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
       => ( ( k1_funct_1 @ B @ D )
          = ( k1_funct_1 @ C @ D ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( zip_tseitin_1 @ D @ C @ A ) )
              & ! [D: $i] :
                  ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13
       != ( k8_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X12 @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,(
    ! [X12: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X12 @ X14 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ ( k8_relat_1 @ X14 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13
       != ( k8_relat_1 @ X14 @ X12 ) )
      | ( zip_tseitin_1 @ X17 @ X12 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,(
    ! [X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ ( k8_relat_1 @ X14 @ X12 ) ) )
      | ( zip_tseitin_1 @ X17 @ X12 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ~ ( zip_tseitin_1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('43',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X9 @ X8 ) @ X10 )
      | ~ ( zip_tseitin_1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['21','41','46','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['21','41','46','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['20','48','50'])).

thf('52',plain,
    ( $false
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['1','51'])).

thf('53',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['21','41','46'])).

thf('54',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['52','53'])).


%------------------------------------------------------------------------------
