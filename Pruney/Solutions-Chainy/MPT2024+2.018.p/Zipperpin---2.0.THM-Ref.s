%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OB2JlW3n0p

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:29 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 497 expanded)
%              Number of leaves         :   25 ( 154 expanded)
%              Depth                    :   20
%              Number of atoms          : 1288 (8824 expanded)
%              Number of equality atoms :   33 ( 155 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t23_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                 => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                   => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_waybel_9])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ? [D: $i] :
                  ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ B @ D )
                  & ( D = C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X17 @ ( sk_D_1 @ X19 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( ( sk_D_1 @ X19 @ X17 @ X18 )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4','5','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['16','17'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X19 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( ( sk_D_1 @ X19 @ X17 @ X18 )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
      = sk_D_2 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
      = sk_D_2 ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X19 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('58',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t39_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
              <=> ( ( r2_hidden @ B @ C )
                  & ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( r2_hidden @ X22 @ ( u1_struct_0 @ ( k9_yellow_6 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['66'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('76',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X19 @ X17 @ X18 ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','98'])).

thf('100',plain,
    ( ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( v3_pre_topc @ ( sk_D_1 @ X19 @ X17 @ X18 ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k9_yellow_6 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( sk_D_1 @ sk_D_2 @ sk_B @ sk_A )
    = sk_D_2 ),
    inference(clc,[status(thm)],['33','34'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_pre_topc @ sk_D_2 @ sk_A ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['100','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','80','81','111','112'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('119',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('120',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_2 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OB2JlW3n0p
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.92/3.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.92/3.16  % Solved by: fo/fo7.sh
% 2.92/3.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.92/3.16  % done 2603 iterations in 2.705s
% 2.92/3.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.92/3.16  % SZS output start Refutation
% 2.92/3.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.92/3.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.92/3.16  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.92/3.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.92/3.16  thf(sk_D_2_type, type, sk_D_2: $i).
% 2.92/3.16  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 2.92/3.16  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.92/3.16  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.92/3.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.92/3.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.92/3.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.92/3.16  thf(sk_C_type, type, sk_C: $i).
% 2.92/3.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.92/3.16  thf(sk_A_type, type, sk_A: $i).
% 2.92/3.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.92/3.16  thf(sk_B_type, type, sk_B: $i).
% 2.92/3.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.92/3.16  thf(t23_waybel_9, conjecture,
% 2.92/3.16    (![A:$i]:
% 2.92/3.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.92/3.16       ( ![B:$i]:
% 2.92/3.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.16           ( ![C:$i]:
% 2.92/3.16             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.92/3.16               ( ![D:$i]:
% 2.92/3.16                 ( ( m1_subset_1 @
% 2.92/3.16                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.92/3.16                   ( m1_subset_1 @
% 2.92/3.16                     ( k2_xboole_0 @ C @ D ) @ 
% 2.92/3.16                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 2.92/3.16  thf(zf_stmt_0, negated_conjecture,
% 2.92/3.16    (~( ![A:$i]:
% 2.92/3.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.92/3.16            ( l1_pre_topc @ A ) ) =>
% 2.92/3.16          ( ![B:$i]:
% 2.92/3.16            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.16              ( ![C:$i]:
% 2.92/3.16                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.92/3.16                  ( ![D:$i]:
% 2.92/3.16                    ( ( m1_subset_1 @
% 2.92/3.16                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.92/3.16                      ( m1_subset_1 @
% 2.92/3.16                        ( k2_xboole_0 @ C @ D ) @ 
% 2.92/3.16                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 2.92/3.16    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 2.92/3.16  thf('0', plain,
% 2.92/3.16      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 2.92/3.16          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('1', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf(t38_yellow_6, axiom,
% 2.92/3.16    (![A:$i]:
% 2.92/3.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.92/3.16       ( ![B:$i]:
% 2.92/3.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.16           ( ![C:$i]:
% 2.92/3.16             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 2.92/3.16               ( ?[D:$i]:
% 2.92/3.16                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 2.92/3.16                   ( ( D ) = ( C ) ) & 
% 2.92/3.16                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 2.92/3.16  thf('2', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | (r2_hidden @ X17 @ (sk_D_1 @ X19 @ X17 @ X18))
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('3', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | (r2_hidden @ sk_B @ (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['1', '2'])).
% 2.92/3.16  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('6', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('7', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | ((sk_D_1 @ X19 @ X17 @ X18) = (X19))
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('8', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['6', '7'])).
% 2.92/3.16  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('12', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 2.92/3.16      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 2.92/3.16  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('14', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 2.92/3.16      inference('clc', [status(thm)], ['12', '13'])).
% 2.92/3.16  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 2.92/3.16      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 2.92/3.16  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 2.92/3.16      inference('clc', [status(thm)], ['16', '17'])).
% 2.92/3.16  thf(d3_xboole_0, axiom,
% 2.92/3.16    (![A:$i,B:$i,C:$i]:
% 2.92/3.16     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.92/3.16       ( ![D:$i]:
% 2.92/3.16         ( ( r2_hidden @ D @ C ) <=>
% 2.92/3.16           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.92/3.16  thf('19', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.92/3.16         (~ (r2_hidden @ X0 @ X3)
% 2.92/3.16          | (r2_hidden @ X0 @ X2)
% 2.92/3.16          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 2.92/3.16      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.92/3.16  thf('20', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.92/3.16         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 2.92/3.16      inference('simplify', [status(thm)], ['19'])).
% 2.92/3.16  thf('21', plain,
% 2.92/3.16      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 2.92/3.16      inference('sup-', [status(thm)], ['18', '20'])).
% 2.92/3.16  thf('22', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('23', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | (m1_subset_1 @ (sk_D_1 @ X19 @ X17 @ X18) @ 
% 2.92/3.16             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('24', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ 
% 2.92/3.16           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['22', '23'])).
% 2.92/3.16  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('27', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('28', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | ((sk_D_1 @ X19 @ X17 @ X18) = (X19))
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('29', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['27', '28'])).
% 2.92/3.16  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('33', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A) | ((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2)))),
% 2.92/3.16      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 2.92/3.16  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('35', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 2.92/3.16      inference('clc', [status(thm)], ['33', '34'])).
% 2.92/3.16  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('37', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | (m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.92/3.16      inference('demod', [status(thm)], ['24', '25', '26', '35', '36'])).
% 2.92/3.16  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('39', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('clc', [status(thm)], ['37', '38'])).
% 2.92/3.16  thf(t3_subset, axiom,
% 2.92/3.16    (![A:$i,B:$i]:
% 2.92/3.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.92/3.16  thf('40', plain,
% 2.92/3.16      (![X11 : $i, X12 : $i]:
% 2.92/3.16         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.92/3.16      inference('cnf', [status(esa)], [t3_subset])).
% 2.92/3.16  thf('41', plain, ((r1_tarski @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['39', '40'])).
% 2.92/3.16  thf('42', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('43', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | (m1_subset_1 @ (sk_D_1 @ X19 @ X17 @ X18) @ 
% 2.92/3.16             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('44', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 2.92/3.16           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['42', '43'])).
% 2.92/3.16  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('47', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 2.92/3.16      inference('clc', [status(thm)], ['12', '13'])).
% 2.92/3.16  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('49', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.92/3.16      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 2.92/3.16  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('51', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('clc', [status(thm)], ['49', '50'])).
% 2.92/3.16  thf('52', plain,
% 2.92/3.16      (![X11 : $i, X12 : $i]:
% 2.92/3.16         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.92/3.16      inference('cnf', [status(esa)], [t3_subset])).
% 2.92/3.16  thf('53', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['51', '52'])).
% 2.92/3.16  thf(t8_xboole_1, axiom,
% 2.92/3.16    (![A:$i,B:$i,C:$i]:
% 2.92/3.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.92/3.16       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.92/3.16  thf('54', plain,
% 2.92/3.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.92/3.16         (~ (r1_tarski @ X6 @ X7)
% 2.92/3.16          | ~ (r1_tarski @ X8 @ X7)
% 2.92/3.16          | (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 2.92/3.16      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.92/3.16  thf('55', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))
% 2.92/3.16          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['53', '54'])).
% 2.92/3.16  thf('56', plain,
% 2.92/3.16      ((r1_tarski @ (k2_xboole_0 @ sk_C @ sk_D_2) @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['41', '55'])).
% 2.92/3.16  thf('57', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((r1_tarski @ (k2_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))
% 2.92/3.16          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['53', '54'])).
% 2.92/3.16  thf('58', plain,
% 2.92/3.16      ((r1_tarski @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)) @ 
% 2.92/3.16        (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['56', '57'])).
% 2.92/3.16  thf('59', plain,
% 2.92/3.16      (![X11 : $i, X13 : $i]:
% 2.92/3.16         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 2.92/3.16      inference('cnf', [status(esa)], [t3_subset])).
% 2.92/3.16  thf('60', plain,
% 2.92/3.16      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)) @ 
% 2.92/3.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['58', '59'])).
% 2.92/3.16  thf(t39_yellow_6, axiom,
% 2.92/3.16    (![A:$i]:
% 2.92/3.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.92/3.16       ( ![B:$i]:
% 2.92/3.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.92/3.16           ( ![C:$i]:
% 2.92/3.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.92/3.16               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 2.92/3.16                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.92/3.16  thf('61', plain,
% 2.92/3.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 2.92/3.16          | ~ (r2_hidden @ X20 @ X22)
% 2.92/3.16          | ~ (v3_pre_topc @ X22 @ X21)
% 2.92/3.16          | (r2_hidden @ X22 @ (u1_struct_0 @ (k9_yellow_6 @ X21 @ X20)))
% 2.92/3.16          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.92/3.16          | ~ (l1_pre_topc @ X21)
% 2.92/3.16          | ~ (v2_pre_topc @ X21)
% 2.92/3.16          | (v2_struct_0 @ X21))),
% 2.92/3.16      inference('cnf', [status(esa)], [t39_yellow_6])).
% 2.92/3.16  thf('62', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((v2_struct_0 @ sk_A)
% 2.92/3.16          | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16          | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16          | (r2_hidden @ 
% 2.92/3.16             (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)) @ 
% 2.92/3.16             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.92/3.16          | ~ (v3_pre_topc @ 
% 2.92/3.16               (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)) @ sk_A)
% 2.92/3.16          | ~ (r2_hidden @ X0 @ 
% 2.92/3.16               (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)))
% 2.92/3.16          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['60', '61'])).
% 2.92/3.16  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('65', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((v2_struct_0 @ sk_A)
% 2.92/3.16          | (r2_hidden @ 
% 2.92/3.16             (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)) @ 
% 2.92/3.16             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.92/3.16          | ~ (v3_pre_topc @ 
% 2.92/3.16               (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)) @ sk_A)
% 2.92/3.16          | ~ (r2_hidden @ X0 @ 
% 2.92/3.16               (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_2)))
% 2.92/3.16          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('demod', [status(thm)], ['62', '63', '64'])).
% 2.92/3.16  thf('66', plain,
% 2.92/3.16      (![X1 : $i, X3 : $i, X5 : $i]:
% 2.92/3.16         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 2.92/3.16          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 2.92/3.16          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 2.92/3.16          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 2.92/3.16      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.92/3.16  thf('67', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.92/3.16          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.92/3.16          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('eq_fact', [status(thm)], ['66'])).
% 2.92/3.16  thf('68', plain,
% 2.92/3.16      (![X1 : $i, X3 : $i, X5 : $i]:
% 2.92/3.16         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 2.92/3.16          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 2.92/3.16          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 2.92/3.16      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.92/3.16  thf('69', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 2.92/3.16          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.92/3.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.92/3.16          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['67', '68'])).
% 2.92/3.16  thf('70', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.92/3.16          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.92/3.16          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('simplify', [status(thm)], ['69'])).
% 2.92/3.16  thf('71', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.92/3.16          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.92/3.16          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('eq_fact', [status(thm)], ['66'])).
% 2.92/3.16  thf('72', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 2.92/3.16          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.92/3.16      inference('clc', [status(thm)], ['70', '71'])).
% 2.92/3.16  thf('73', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i, X3 : $i]:
% 2.92/3.16         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 2.92/3.16      inference('simplify', [status(thm)], ['19'])).
% 2.92/3.16  thf('74', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.92/3.16         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 2.92/3.16          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['72', '73'])).
% 2.92/3.16  thf('75', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 2.92/3.16          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.92/3.16      inference('clc', [status(thm)], ['70', '71'])).
% 2.92/3.16  thf('76', plain,
% 2.92/3.16      (![X1 : $i, X3 : $i, X5 : $i]:
% 2.92/3.16         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 2.92/3.16          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 2.92/3.16          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 2.92/3.16      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.92/3.16  thf('77', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 2.92/3.16          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 2.92/3.16          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['75', '76'])).
% 2.92/3.16  thf('78', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 2.92/3.16          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 2.92/3.16      inference('simplify', [status(thm)], ['77'])).
% 2.92/3.16  thf('79', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         (((k2_xboole_0 @ X1 @ X0)
% 2.92/3.16            = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.92/3.16          | ((k2_xboole_0 @ X1 @ X0)
% 2.92/3.16              = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.92/3.16      inference('sup-', [status(thm)], ['74', '78'])).
% 2.92/3.16  thf('80', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         ((k2_xboole_0 @ X1 @ X0)
% 2.92/3.16           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('simplify', [status(thm)], ['79'])).
% 2.92/3.16  thf('81', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         ((k2_xboole_0 @ X1 @ X0)
% 2.92/3.16           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('simplify', [status(thm)], ['79'])).
% 2.92/3.16  thf('82', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('clc', [status(thm)], ['37', '38'])).
% 2.92/3.16  thf('83', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('clc', [status(thm)], ['49', '50'])).
% 2.92/3.16  thf(fc7_tops_1, axiom,
% 2.92/3.16    (![A:$i,B:$i,C:$i]:
% 2.92/3.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 2.92/3.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 2.92/3.16         ( v3_pre_topc @ C @ A ) & 
% 2.92/3.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.92/3.16       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 2.92/3.16  thf('84', plain,
% 2.92/3.16      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.92/3.16          | ~ (v3_pre_topc @ X14 @ X15)
% 2.92/3.16          | ~ (l1_pre_topc @ X15)
% 2.92/3.16          | ~ (v2_pre_topc @ X15)
% 2.92/3.16          | ~ (v3_pre_topc @ X16 @ X15)
% 2.92/3.16          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.92/3.16          | (v3_pre_topc @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 2.92/3.16      inference('cnf', [status(esa)], [fc7_tops_1])).
% 2.92/3.16  thf('85', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 2.92/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.92/3.16          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.92/3.16          | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16          | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['83', '84'])).
% 2.92/3.16  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('88', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 2.92/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.92/3.16          | ~ (v3_pre_topc @ X0 @ sk_A)
% 2.92/3.16          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 2.92/3.16      inference('demod', [status(thm)], ['85', '86', '87'])).
% 2.92/3.16  thf('89', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('90', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | (v3_pre_topc @ (sk_D_1 @ X19 @ X17 @ X18) @ X18)
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('91', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | (v3_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['89', '90'])).
% 2.92/3.16  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('94', plain, (((sk_D_1 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 2.92/3.16      inference('clc', [status(thm)], ['12', '13'])).
% 2.92/3.16  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('96', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 2.92/3.16      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 2.92/3.16  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('98', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 2.92/3.16      inference('clc', [status(thm)], ['96', '97'])).
% 2.92/3.16  thf('99', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 2.92/3.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.92/3.16          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 2.92/3.16      inference('demod', [status(thm)], ['88', '98'])).
% 2.92/3.16  thf('100', plain,
% 2.92/3.16      ((~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 2.92/3.16        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_2) @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['82', '99'])).
% 2.92/3.16  thf('101', plain,
% 2.92/3.16      ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('102', plain,
% 2.92/3.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.92/3.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.92/3.16          | (v3_pre_topc @ (sk_D_1 @ X19 @ X17 @ X18) @ X18)
% 2.92/3.16          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ (k9_yellow_6 @ X18 @ X17)))
% 2.92/3.16          | ~ (l1_pre_topc @ X18)
% 2.92/3.16          | ~ (v2_pre_topc @ X18)
% 2.92/3.16          | (v2_struct_0 @ X18))),
% 2.92/3.16      inference('cnf', [status(esa)], [t38_yellow_6])).
% 2.92/3.16  thf('103', plain,
% 2.92/3.16      (((v2_struct_0 @ sk_A)
% 2.92/3.16        | ~ (v2_pre_topc @ sk_A)
% 2.92/3.16        | ~ (l1_pre_topc @ sk_A)
% 2.92/3.16        | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_A) @ sk_A)
% 2.92/3.16        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['101', '102'])).
% 2.92/3.16  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('106', plain, (((sk_D_1 @ sk_D_2 @ sk_B @ sk_A) = (sk_D_2))),
% 2.92/3.16      inference('clc', [status(thm)], ['33', '34'])).
% 2.92/3.16  thf('107', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('108', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_2 @ sk_A))),
% 2.92/3.16      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 2.92/3.16  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('110', plain, ((v3_pre_topc @ sk_D_2 @ sk_A)),
% 2.92/3.16      inference('clc', [status(thm)], ['108', '109'])).
% 2.92/3.16  thf('111', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_2) @ sk_A)),
% 2.92/3.16      inference('demod', [status(thm)], ['100', '110'])).
% 2.92/3.16  thf('112', plain,
% 2.92/3.16      (![X0 : $i, X1 : $i]:
% 2.92/3.16         ((k2_xboole_0 @ X1 @ X0)
% 2.92/3.16           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.92/3.16      inference('simplify', [status(thm)], ['79'])).
% 2.92/3.16  thf('113', plain,
% 2.92/3.16      (![X0 : $i]:
% 2.92/3.16         ((v2_struct_0 @ sk_A)
% 2.92/3.16          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 2.92/3.16             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 2.92/3.16          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_2))
% 2.92/3.16          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.92/3.16      inference('demod', [status(thm)], ['65', '80', '81', '111', '112'])).
% 2.92/3.16  thf('114', plain,
% 2.92/3.16      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.92/3.16        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 2.92/3.16           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 2.92/3.16        | (v2_struct_0 @ sk_A))),
% 2.92/3.16      inference('sup-', [status(thm)], ['21', '113'])).
% 2.92/3.16  thf('115', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('116', plain,
% 2.92/3.16      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 2.92/3.16         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 2.92/3.16        | (v2_struct_0 @ sk_A))),
% 2.92/3.16      inference('demod', [status(thm)], ['114', '115'])).
% 2.92/3.16  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 2.92/3.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.16  thf('118', plain,
% 2.92/3.16      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 2.92/3.16        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('clc', [status(thm)], ['116', '117'])).
% 2.92/3.16  thf(t1_subset, axiom,
% 2.92/3.16    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.92/3.16  thf('119', plain,
% 2.92/3.16      (![X9 : $i, X10 : $i]:
% 2.92/3.16         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 2.92/3.16      inference('cnf', [status(esa)], [t1_subset])).
% 2.92/3.16  thf('120', plain,
% 2.92/3.16      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_2) @ 
% 2.92/3.16        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 2.92/3.16      inference('sup-', [status(thm)], ['118', '119'])).
% 2.92/3.16  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 2.92/3.16  
% 2.92/3.16  % SZS output end Refutation
% 2.92/3.16  
% 2.92/3.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
