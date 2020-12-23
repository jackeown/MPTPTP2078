%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oVwfrWsFYg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 835 expanded)
%              Number of leaves         :   36 ( 253 expanded)
%              Depth                    :   24
%              Number of atoms          : 1235 (15142 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t84_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( r2_xboole_0 @ C @ D )
                  <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ( ( r2_xboole_0 @ C @ D )
                    <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_orders_2])).

thf('0',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ X20 @ ( u1_struct_0 @ X21 ) ) ) @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t78_orders_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X22 @ ( u1_struct_0 @ X23 ) ) @ X24 )
      | ~ ( m2_orders_2 @ X24 @ X23 @ X22 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m2_orders_2 @ X13 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X16 @ X14 )
      | ~ ( m1_orders_2 @ X16 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D )
      | ( r1_tarski @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('49',plain,
    ( ( ( sk_C = sk_D )
      | ( r2_xboole_0 @ sk_C @ sk_D ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
   <= ~ ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ( sk_C = sk_D )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t69_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ C )
                  & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_orders_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','68'])).

thf('70',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('72',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('75',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['24','79'])).

thf('81',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','80','81'])).

thf('83',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('84',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( C != D )
                   => ( ( m1_orders_2 @ C @ A @ D )
                    <=> ~ ( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_orders_1 @ X25 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m2_orders_2 @ X27 @ X26 @ X25 )
      | ( m1_orders_2 @ X27 @ X26 @ X28 )
      | ( m1_orders_2 @ X28 @ X26 @ X27 )
      | ( X28 = X27 )
      | ~ ( m2_orders_2 @ X28 @ X26 @ X25 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( m1_orders_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('97',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ X16 @ X14 )
      | ~ ( m1_orders_2 @ X16 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
    | ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('108',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','80'])).

thf('109',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('113',plain,
    ( ( r1_tarski @ sk_C @ sk_D )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('114',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('115',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( sk_D = sk_C ) )
   <= ( r2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r2_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['3','80','81'])).

thf('117',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( sk_D = sk_C ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_C = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['110','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['83','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('123',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    $false ),
    inference('sup-',[status(thm)],['121','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oVwfrWsFYg
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 123 iterations in 0.054s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.52  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(t84_orders_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D) | (r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D) | ~ (r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)) | ~ ((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t78_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( m2_orders_2 @
% 0.20/0.52             ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | (m2_orders_2 @ 
% 0.20/0.52             (k1_tarski @ (k1_funct_1 @ X20 @ (u1_struct_0 @ X21))) @ X21 @ X20)
% 0.20/0.52          | ~ (l1_orders_2 @ X21)
% 0.20/0.52          | ~ (v5_orders_2 @ X21)
% 0.20/0.52          | ~ (v4_orders_2 @ X21)
% 0.20/0.52          | ~ (v3_orders_2 @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t78_orders_2])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52        | (m2_orders_2 @ 
% 0.20/0.52           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.20/0.52           sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (m2_orders_2 @ 
% 0.20/0.52           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.20/0.52           sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.20/0.52  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((m2_orders_2 @ 
% 0.20/0.52        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ sk_B)),
% 0.20/0.52      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t79_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (m1_orders_1 @ X22 @ (k1_orders_1 @ (u1_struct_0 @ X23)))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X22 @ (u1_struct_0 @ X23)) @ X24)
% 0.20/0.52          | ~ (m2_orders_2 @ X24 @ X23 @ X22)
% 0.20/0.52          | ~ (l1_orders_2 @ X23)
% 0.20/0.52          | ~ (v5_orders_2 @ X23)
% 0.20/0.52          | ~ (v4_orders_2 @ X23)
% 0.20/0.52          | ~ (v3_orders_2 @ X23)
% 0.20/0.52          | (v2_struct_0 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.52  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.52        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('26', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m2_orders_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.52         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52           ( ( v6_orders_2 @ C @ A ) & 
% 0.20/0.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ X11)
% 0.20/0.52          | ~ (v5_orders_2 @ X11)
% 0.20/0.52          | ~ (v4_orders_2 @ X11)
% 0.20/0.52          | ~ (v3_orders_2 @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11)
% 0.20/0.52          | ~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ~ (m2_orders_2 @ X13 @ X11 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.52  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '36'])).
% 0.20/0.52  thf(t67_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | (r1_tarski @ X16 @ X14)
% 0.20/0.52          | ~ (m1_orders_2 @ X16 @ X15 @ X14)
% 0.20/0.52          | ~ (l1_orders_2 @ X15)
% 0.20/0.52          | ~ (v5_orders_2 @ X15)
% 0.20/0.52          | ~ (v4_orders_2 @ X15)
% 0.20/0.52          | ~ (v3_orders_2 @ X15)
% 0.20/0.52          | (v2_struct_0 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.20/0.52  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ sk_D) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D))),
% 0.20/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((r1_tarski @ sk_C @ sk_D)) <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '46'])).
% 0.20/0.52  thf(d8_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (((((sk_C) = (sk_D)) | (r2_xboole_0 @ sk_C @ sk_D)))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((~ (r2_xboole_0 @ sk_C @ sk_D)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((((sk_C) = (sk_D)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.52         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf(t69_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ((X17) = (k1_xboole_0))
% 0.20/0.52          | ~ (m1_orders_2 @ X19 @ X18 @ X17)
% 0.20/0.52          | ~ (m1_orders_2 @ X17 @ X18 @ X19)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (l1_orders_2 @ X18)
% 0.20/0.52          | ~ (v5_orders_2 @ X18)
% 0.20/0.52          | ~ (v4_orders_2 @ X18)
% 0.20/0.52          | ~ (v3_orders_2 @ X18)
% 0.20/0.52          | (v2_struct_0 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0))
% 0.20/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.20/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '64'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.20/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.52  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.20/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '68'])).
% 0.20/0.52  thf('70', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf(t63_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.20/0.52          | ~ (r2_hidden @ X6 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((m1_subset_1 @ 
% 0.20/0.52        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.52        (k1_zfmisc_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.52  thf(t5_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.52          | ~ (v1_xboole_0 @ X10)
% 0.20/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ sk_C)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ 
% 0.20/0.52               (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.52           | ~ (r2_hidden @ X0 @ 
% 0.20/0.52                (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '76'])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ~ (r2_hidden @ X0 @ 
% 0.20/0.52             (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.20/0.52         <= (~ ((r2_xboole_0 @ sk_C @ sk_D)) & 
% 0.20/0.52             ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) | ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '79'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('82', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '80', '81'])).
% 0.20/0.52  thf('83', plain, ((r2_xboole_0 @ sk_C @ sk_D)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '82'])).
% 0.20/0.52  thf('84', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('85', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t83_orders_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.20/0.52                   ( ( ( C ) != ( D ) ) =>
% 0.20/0.52                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.20/0.52                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.52         (~ (m1_orders_1 @ X25 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.20/0.52          | ~ (m2_orders_2 @ X27 @ X26 @ X25)
% 0.20/0.52          | (m1_orders_2 @ X27 @ X26 @ X28)
% 0.20/0.52          | (m1_orders_2 @ X28 @ X26 @ X27)
% 0.20/0.52          | ((X28) = (X27))
% 0.20/0.52          | ~ (m2_orders_2 @ X28 @ X26 @ X25)
% 0.20/0.52          | ~ (l1_orders_2 @ X26)
% 0.20/0.52          | ~ (v5_orders_2 @ X26)
% 0.20/0.52          | ~ (v4_orders_2 @ X26)
% 0.20/0.52          | ~ (v3_orders_2 @ X26)
% 0.20/0.52          | (v2_struct_0 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | ((X0) = (X1))
% 0.20/0.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.52  thf('89', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('90', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('91', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | ((X0) = (X1))
% 0.20/0.52          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.20/0.52          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.20/0.52          | ((sk_C) = (X0))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['85', '93'])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((sk_C) = (sk_D))
% 0.20/0.52        | (m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.20/0.52        | (m1_orders_2 @ sk_D @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['84', '94'])).
% 0.20/0.52  thf('96', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | (r1_tarski @ X16 @ X14)
% 0.20/0.52          | ~ (m1_orders_2 @ X16 @ X15 @ X14)
% 0.20/0.52          | ~ (l1_orders_2 @ X15)
% 0.20/0.52          | ~ (v5_orders_2 @ X15)
% 0.20/0.52          | ~ (v4_orders_2 @ X15)
% 0.20/0.52          | ~ (v3_orders_2 @ X15)
% 0.20/0.52          | (v2_struct_0 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.52          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.52          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.52  thf('99', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('100', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('101', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.52          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.20/0.52  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.20/0.52      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.52  thf('106', plain,
% 0.20/0.52      (((m1_orders_2 @ sk_C @ sk_A @ sk_D)
% 0.20/0.52        | ((sk_C) = (sk_D))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | (r1_tarski @ sk_D @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['95', '105'])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D))
% 0.20/0.52         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('108', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '80'])).
% 0.20/0.52  thf('109', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (((r1_tarski @ sk_D @ sk_C) | (v2_struct_0 @ sk_A) | ((sk_C) = (sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['106', '109'])).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      (((r2_xboole_0 @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('112', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (((r1_tarski @ sk_C @ sk_D)) <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('114', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('115', plain,
% 0.20/0.52      (((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C))))
% 0.20/0.52         <= (((r2_xboole_0 @ sk_C @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.52  thf('116', plain, (((r2_xboole_0 @ sk_C @ sk_D))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['3', '80', '81'])).
% 0.20/0.52  thf('117', plain, ((~ (r1_tarski @ sk_D @ sk_C) | ((sk_D) = (sk_C)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 0.20/0.52  thf('118', plain, ((((sk_C) = (sk_D)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['110', '117'])).
% 0.20/0.52  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('120', plain, (((sk_C) = (sk_D))),
% 0.20/0.52      inference('clc', [status(thm)], ['118', '119'])).
% 0.20/0.52  thf('121', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['83', '120'])).
% 0.20/0.52  thf('122', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.52  thf('123', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['122'])).
% 0.20/0.52  thf('124', plain, ($false), inference('sup-', [status(thm)], ['121', '123'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
