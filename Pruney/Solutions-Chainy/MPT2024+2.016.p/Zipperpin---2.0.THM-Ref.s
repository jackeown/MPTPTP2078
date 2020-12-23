%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xGK9s8qJpr

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:28 EST 2020

% Result     : Theorem 26.79s
% Output     : Refutation 26.79s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 464 expanded)
%              Number of leaves         :   29 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          : 1241 (8328 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r2_hidden @ X26 @ ( sk_D_2 @ X28 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( sk_D_2 @ X28 @ X26 @ X27 )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
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
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
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
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X28 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( sk_D_2 @ X28 @ X26 @ X27 )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
      = sk_D_3 )
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
    | ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
      = sk_D_3 ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
    = sk_D_3 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X28 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_3 )
    = ( k2_xboole_0 @ sk_C @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','57'])).

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

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( v3_pre_topc @ X31 @ X30 )
      | ( r2_hidden @ X31 @ ( u1_struct_0 @ ( k9_yellow_6 @ X30 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( v3_pre_topc @ ( sk_D_2 @ X28 @ X26 @ X27 ) @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['12','13'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','80'])).

thf('82',plain,
    ( ~ ( v3_pre_topc @ sk_D_3 @ sk_A )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D_3 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( v3_pre_topc @ ( sk_D_2 @ X28 @ X26 @ X27 ) @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k9_yellow_6 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_6])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_D_2 @ sk_D_3 @ sk_B @ sk_A )
    = sk_D_3 ),
    inference(clc,[status(thm)],['33','34'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D_3 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_pre_topc @ sk_D_3 @ sk_A ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ sk_A ),
    inference(demod,[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','93'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('100',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('101',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('104',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X16 @ X15 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X14 @ X16 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(clc,[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_3 ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xGK9s8qJpr
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 26.79/26.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.79/26.99  % Solved by: fo/fo7.sh
% 26.79/26.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.79/26.99  % done 11554 iterations in 26.537s
% 26.79/26.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.79/26.99  % SZS output start Refutation
% 26.79/26.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.79/26.99  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 26.79/26.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 26.79/26.99  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 26.79/26.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.79/26.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 26.79/26.99  thf(sk_D_3_type, type, sk_D_3: $i).
% 26.79/26.99  thf(sk_C_type, type, sk_C: $i).
% 26.79/26.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 26.79/26.99  thf(sk_A_type, type, sk_A: $i).
% 26.79/26.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 26.79/26.99  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 26.79/26.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 26.79/26.99  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 26.79/26.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 26.79/26.99  thf(sk_B_type, type, sk_B: $i).
% 26.79/26.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 26.79/26.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.79/26.99  thf(t23_waybel_9, conjecture,
% 26.79/26.99    (![A:$i]:
% 26.79/26.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.79/26.99       ( ![B:$i]:
% 26.79/26.99         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.79/26.99           ( ![C:$i]:
% 26.79/26.99             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 26.79/26.99               ( ![D:$i]:
% 26.79/26.99                 ( ( m1_subset_1 @
% 26.79/26.99                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 26.79/26.99                   ( m1_subset_1 @
% 26.79/26.99                     ( k2_xboole_0 @ C @ D ) @ 
% 26.79/26.99                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 26.79/26.99  thf(zf_stmt_0, negated_conjecture,
% 26.79/26.99    (~( ![A:$i]:
% 26.79/26.99        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 26.79/26.99            ( l1_pre_topc @ A ) ) =>
% 26.79/26.99          ( ![B:$i]:
% 26.79/26.99            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.79/26.99              ( ![C:$i]:
% 26.79/26.99                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 26.79/26.99                  ( ![D:$i]:
% 26.79/26.99                    ( ( m1_subset_1 @
% 26.79/26.99                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 26.79/26.99                      ( m1_subset_1 @
% 26.79/26.99                        ( k2_xboole_0 @ C @ D ) @ 
% 26.79/26.99                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 26.79/26.99    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 26.79/26.99  thf('0', plain,
% 26.79/26.99      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('1', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf(t38_yellow_6, axiom,
% 26.79/26.99    (![A:$i]:
% 26.79/26.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.79/26.99       ( ![B:$i]:
% 26.79/26.99         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.79/26.99           ( ![C:$i]:
% 26.79/26.99             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 26.79/26.99               ( ?[D:$i]:
% 26.79/26.99                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 26.79/26.99                   ( ( D ) = ( C ) ) & 
% 26.79/26.99                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 26.79/26.99  thf('2', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | (r2_hidden @ X26 @ (sk_D_2 @ X28 @ X26 @ X27))
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('3', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | (r2_hidden @ sk_B @ (sk_D_2 @ sk_C @ sk_B @ sk_A))
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['1', '2'])).
% 26.79/26.99  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('6', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('7', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | ((sk_D_2 @ X28 @ X26 @ X27) = (X28))
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('8', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | ((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['6', '7'])).
% 26.79/26.99  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('12', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A) | ((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C)))),
% 26.79/26.99      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 26.79/26.99  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('14', plain, (((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 26.79/26.99      inference('clc', [status(thm)], ['12', '13'])).
% 26.79/26.99  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('16', plain, (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ sk_C))),
% 26.79/26.99      inference('demod', [status(thm)], ['3', '4', '5', '14', '15'])).
% 26.79/26.99  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('18', plain, ((r2_hidden @ sk_B @ sk_C)),
% 26.79/26.99      inference('clc', [status(thm)], ['16', '17'])).
% 26.79/26.99  thf(d3_xboole_0, axiom,
% 26.79/26.99    (![A:$i,B:$i,C:$i]:
% 26.79/26.99     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 26.79/26.99       ( ![D:$i]:
% 26.79/26.99         ( ( r2_hidden @ D @ C ) <=>
% 26.79/26.99           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 26.79/26.99  thf('19', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.79/26.99         (~ (r2_hidden @ X0 @ X3)
% 26.79/26.99          | (r2_hidden @ X0 @ X2)
% 26.79/26.99          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 26.79/26.99      inference('cnf', [status(esa)], [d3_xboole_0])).
% 26.79/26.99  thf('20', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i, X3 : $i]:
% 26.79/26.99         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 26.79/26.99      inference('simplify', [status(thm)], ['19'])).
% 26.79/26.99  thf('21', plain,
% 26.79/26.99      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 26.79/26.99      inference('sup-', [status(thm)], ['18', '20'])).
% 26.79/26.99  thf('22', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('23', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | (m1_subset_1 @ (sk_D_2 @ X28 @ X26 @ X27) @ 
% 26.79/26.99             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('24', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_A) @ 
% 26.79/26.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['22', '23'])).
% 26.79/26.99  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('27', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('28', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | ((sk_D_2 @ X28 @ X26 @ X27) = (X28))
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('29', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | ((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3))
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['27', '28'])).
% 26.79/26.99  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('33', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A) | ((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3)))),
% 26.79/26.99      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 26.79/26.99  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('35', plain, (((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3))),
% 26.79/26.99      inference('clc', [status(thm)], ['33', '34'])).
% 26.79/26.99  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('37', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | (m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 26.79/26.99      inference('demod', [status(thm)], ['24', '25', '26', '35', '36'])).
% 26.79/26.99  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('39', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('clc', [status(thm)], ['37', '38'])).
% 26.79/26.99  thf('40', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('41', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | (m1_subset_1 @ (sk_D_2 @ X28 @ X26 @ X27) @ 
% 26.79/26.99             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('42', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | (m1_subset_1 @ (sk_D_2 @ sk_C @ sk_B @ sk_A) @ 
% 26.79/26.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['40', '41'])).
% 26.79/26.99  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('45', plain, (((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 26.79/26.99      inference('clc', [status(thm)], ['12', '13'])).
% 26.79/26.99  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('47', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 26.79/26.99      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 26.79/26.99  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('49', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('clc', [status(thm)], ['47', '48'])).
% 26.79/26.99  thf(dt_k4_subset_1, axiom,
% 26.79/26.99    (![A:$i,B:$i,C:$i]:
% 26.79/26.99     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 26.79/26.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 26.79/26.99       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 26.79/26.99  thf('50', plain,
% 26.79/26.99      (![X8 : $i, X9 : $i, X10 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 26.79/26.99          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9))
% 26.79/26.99          | (m1_subset_1 @ (k4_subset_1 @ X9 @ X8 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 26.79/26.99      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 26.79/26.99  thf('51', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 26.79/26.99           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 26.79/26.99      inference('sup-', [status(thm)], ['49', '50'])).
% 26.79/26.99  thf('52', plain,
% 26.79/26.99      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_3) @ 
% 26.79/26.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['39', '51'])).
% 26.79/26.99  thf('53', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('clc', [status(thm)], ['37', '38'])).
% 26.79/26.99  thf('54', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('clc', [status(thm)], ['47', '48'])).
% 26.79/26.99  thf(redefinition_k4_subset_1, axiom,
% 26.79/26.99    (![A:$i,B:$i,C:$i]:
% 26.79/26.99     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 26.79/26.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 26.79/26.99       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 26.79/26.99  thf('55', plain,
% 26.79/26.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 26.79/26.99          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 26.79/26.99          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 26.79/26.99      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 26.79/26.99  thf('56', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 26.79/26.99            = (k2_xboole_0 @ sk_C @ X0))
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 26.79/26.99      inference('sup-', [status(thm)], ['54', '55'])).
% 26.79/26.99  thf('57', plain,
% 26.79/26.99      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_3)
% 26.79/26.99         = (k2_xboole_0 @ sk_C @ sk_D_3))),
% 26.79/26.99      inference('sup-', [status(thm)], ['53', '56'])).
% 26.79/26.99  thf('58', plain,
% 26.79/26.99      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('demod', [status(thm)], ['52', '57'])).
% 26.79/26.99  thf(t39_yellow_6, axiom,
% 26.79/26.99    (![A:$i]:
% 26.79/26.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.79/26.99       ( ![B:$i]:
% 26.79/26.99         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.79/26.99           ( ![C:$i]:
% 26.79/26.99             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.79/26.99               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 26.79/26.99                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 26.79/26.99  thf('59', plain,
% 26.79/26.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 26.79/26.99          | ~ (r2_hidden @ X29 @ X31)
% 26.79/26.99          | ~ (v3_pre_topc @ X31 @ X30)
% 26.79/26.99          | (r2_hidden @ X31 @ (u1_struct_0 @ (k9_yellow_6 @ X30 @ X29)))
% 26.79/26.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 26.79/26.99          | ~ (l1_pre_topc @ X30)
% 26.79/26.99          | ~ (v2_pre_topc @ X30)
% 26.79/26.99          | (v2_struct_0 @ X30))),
% 26.79/26.99      inference('cnf', [status(esa)], [t39_yellow_6])).
% 26.79/26.99  thf('60', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((v2_struct_0 @ sk_A)
% 26.79/26.99          | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99          | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 26.79/26.99          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A)
% 26.79/26.99          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_3))
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['58', '59'])).
% 26.79/26.99  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('63', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((v2_struct_0 @ sk_A)
% 26.79/26.99          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 26.79/26.99          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A)
% 26.79/26.99          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_3))
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('demod', [status(thm)], ['60', '61', '62'])).
% 26.79/26.99  thf('64', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('clc', [status(thm)], ['37', '38'])).
% 26.79/26.99  thf('65', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('clc', [status(thm)], ['47', '48'])).
% 26.79/26.99  thf(fc7_tops_1, axiom,
% 26.79/26.99    (![A:$i,B:$i,C:$i]:
% 26.79/26.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 26.79/26.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 26.79/26.99         ( v3_pre_topc @ C @ A ) & 
% 26.79/26.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 26.79/26.99       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 26.79/26.99  thf('66', plain,
% 26.79/26.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 26.79/26.99          | ~ (v3_pre_topc @ X23 @ X24)
% 26.79/26.99          | ~ (l1_pre_topc @ X24)
% 26.79/26.99          | ~ (v2_pre_topc @ X24)
% 26.79/26.99          | ~ (v3_pre_topc @ X25 @ X24)
% 26.79/26.99          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 26.79/26.99          | (v3_pre_topc @ (k2_xboole_0 @ X23 @ X25) @ X24))),
% 26.79/26.99      inference('cnf', [status(esa)], [fc7_tops_1])).
% 26.79/26.99  thf('67', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.79/26.99          | ~ (v3_pre_topc @ X0 @ sk_A)
% 26.79/26.99          | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99          | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 26.79/26.99      inference('sup-', [status(thm)], ['65', '66'])).
% 26.79/26.99  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('70', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.79/26.99          | ~ (v3_pre_topc @ X0 @ sk_A)
% 26.79/26.99          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 26.79/26.99      inference('demod', [status(thm)], ['67', '68', '69'])).
% 26.79/26.99  thf('71', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('72', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | (v3_pre_topc @ (sk_D_2 @ X28 @ X26 @ X27) @ X27)
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('73', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | (v3_pre_topc @ (sk_D_2 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['71', '72'])).
% 26.79/26.99  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('76', plain, (((sk_D_2 @ sk_C @ sk_B @ sk_A) = (sk_C))),
% 26.79/26.99      inference('clc', [status(thm)], ['12', '13'])).
% 26.79/26.99  thf('77', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('78', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_C @ sk_A))),
% 26.79/26.99      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 26.79/26.99  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('80', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 26.79/26.99      inference('clc', [status(thm)], ['78', '79'])).
% 26.79/26.99  thf('81', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.79/26.99          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 26.79/26.99      inference('demod', [status(thm)], ['70', '80'])).
% 26.79/26.99  thf('82', plain,
% 26.79/26.99      ((~ (v3_pre_topc @ sk_D_3 @ sk_A)
% 26.79/26.99        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A))),
% 26.79/26.99      inference('sup-', [status(thm)], ['64', '81'])).
% 26.79/26.99  thf('83', plain,
% 26.79/26.99      ((m1_subset_1 @ sk_D_3 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('84', plain,
% 26.79/26.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 26.79/26.99          | (v3_pre_topc @ (sk_D_2 @ X28 @ X26 @ X27) @ X27)
% 26.79/26.99          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k9_yellow_6 @ X27 @ X26)))
% 26.79/26.99          | ~ (l1_pre_topc @ X27)
% 26.79/26.99          | ~ (v2_pre_topc @ X27)
% 26.79/26.99          | (v2_struct_0 @ X27))),
% 26.79/26.99      inference('cnf', [status(esa)], [t38_yellow_6])).
% 26.79/26.99  thf('85', plain,
% 26.79/26.99      (((v2_struct_0 @ sk_A)
% 26.79/26.99        | ~ (v2_pre_topc @ sk_A)
% 26.79/26.99        | ~ (l1_pre_topc @ sk_A)
% 26.79/26.99        | (v3_pre_topc @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_A) @ sk_A)
% 26.79/26.99        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['83', '84'])).
% 26.79/26.99  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('88', plain, (((sk_D_2 @ sk_D_3 @ sk_B @ sk_A) = (sk_D_3))),
% 26.79/26.99      inference('clc', [status(thm)], ['33', '34'])).
% 26.79/26.99  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('90', plain, (((v2_struct_0 @ sk_A) | (v3_pre_topc @ sk_D_3 @ sk_A))),
% 26.79/26.99      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 26.79/26.99  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('92', plain, ((v3_pre_topc @ sk_D_3 @ sk_A)),
% 26.79/26.99      inference('clc', [status(thm)], ['90', '91'])).
% 26.79/26.99  thf('93', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D_3) @ sk_A)),
% 26.79/26.99      inference('demod', [status(thm)], ['82', '92'])).
% 26.79/26.99  thf('94', plain,
% 26.79/26.99      (![X0 : $i]:
% 26.79/26.99         ((v2_struct_0 @ sk_A)
% 26.79/26.99          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 26.79/26.99          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D_3))
% 26.79/26.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 26.79/26.99      inference('demod', [status(thm)], ['63', '93'])).
% 26.79/26.99  thf('95', plain,
% 26.79/26.99      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 26.79/26.99        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 26.79/26.99        | (v2_struct_0 @ sk_A))),
% 26.79/26.99      inference('sup-', [status(thm)], ['21', '94'])).
% 26.79/26.99  thf('96', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('97', plain,
% 26.79/26.99      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 26.79/26.99        | (v2_struct_0 @ sk_A))),
% 26.79/26.99      inference('demod', [status(thm)], ['95', '96'])).
% 26.79/26.99  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 26.79/26.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.79/26.99  thf('99', plain,
% 26.79/26.99      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('clc', [status(thm)], ['97', '98'])).
% 26.79/26.99  thf(t7_xboole_1, axiom,
% 26.79/26.99    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 26.79/26.99  thf('100', plain,
% 26.79/26.99      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 26.79/26.99      inference('cnf', [status(esa)], [t7_xboole_1])).
% 26.79/26.99  thf(t3_subset, axiom,
% 26.79/26.99    (![A:$i,B:$i]:
% 26.79/26.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 26.79/26.99  thf('101', plain,
% 26.79/26.99      (![X17 : $i, X19 : $i]:
% 26.79/26.99         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 26.79/26.99      inference('cnf', [status(esa)], [t3_subset])).
% 26.79/26.99  thf('102', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]:
% 26.79/26.99         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['100', '101'])).
% 26.79/26.99  thf('103', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]:
% 26.79/26.99         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['100', '101'])).
% 26.79/26.99  thf(t7_subset_1, axiom,
% 26.79/26.99    (![A:$i,B:$i]:
% 26.79/26.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 26.79/26.99       ( ![C:$i]:
% 26.79/26.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 26.79/26.99           ( ( ![D:$i]:
% 26.79/26.99               ( ( m1_subset_1 @ D @ A ) =>
% 26.79/26.99                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 26.79/26.99             ( r1_tarski @ B @ C ) ) ) ) ))).
% 26.79/26.99  thf('104', plain,
% 26.79/26.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 26.79/26.99          | (r1_tarski @ X16 @ X14)
% 26.79/26.99          | (r2_hidden @ (sk_D_1 @ X14 @ X16 @ X15) @ X16)
% 26.79/26.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 26.79/26.99      inference('cnf', [status(esa)], [t7_subset_1])).
% 26.79/26.99  thf('105', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 26.79/26.99          | (r2_hidden @ (sk_D_1 @ X1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 26.79/26.99          | (r1_tarski @ X2 @ X1))),
% 26.79/26.99      inference('sup-', [status(thm)], ['103', '104'])).
% 26.79/26.99  thf('106', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]:
% 26.79/26.99         ((r1_tarski @ X1 @ X1)
% 26.79/26.99          | (r2_hidden @ (sk_D_1 @ X1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ X1))),
% 26.79/26.99      inference('sup-', [status(thm)], ['102', '105'])).
% 26.79/26.99  thf('107', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]:
% 26.79/26.99         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['100', '101'])).
% 26.79/26.99  thf('108', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]:
% 26.79/26.99         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['100', '101'])).
% 26.79/26.99  thf('109', plain,
% 26.79/26.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 26.79/26.99          | (r1_tarski @ X16 @ X14)
% 26.79/26.99          | ~ (r2_hidden @ (sk_D_1 @ X14 @ X16 @ X15) @ X14)
% 26.79/26.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 26.79/26.99      inference('cnf', [status(esa)], [t7_subset_1])).
% 26.79/26.99  thf('110', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.79/26.99         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 26.79/26.99          | ~ (r2_hidden @ (sk_D_1 @ X1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 26.79/26.99          | (r1_tarski @ X2 @ X1))),
% 26.79/26.99      inference('sup-', [status(thm)], ['108', '109'])).
% 26.79/26.99  thf('111', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]:
% 26.79/26.99         ((r1_tarski @ X1 @ X1)
% 26.79/26.99          | ~ (r2_hidden @ (sk_D_1 @ X1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ X1))),
% 26.79/26.99      inference('sup-', [status(thm)], ['107', '110'])).
% 26.79/26.99  thf('112', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 26.79/26.99      inference('clc', [status(thm)], ['106', '111'])).
% 26.79/26.99  thf('113', plain,
% 26.79/26.99      (![X17 : $i, X19 : $i]:
% 26.79/26.99         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 26.79/26.99      inference('cnf', [status(esa)], [t3_subset])).
% 26.79/26.99  thf('114', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 26.79/26.99      inference('sup-', [status(thm)], ['112', '113'])).
% 26.79/26.99  thf(t4_subset, axiom,
% 26.79/26.99    (![A:$i,B:$i,C:$i]:
% 26.79/26.99     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 26.79/26.99       ( m1_subset_1 @ A @ C ) ))).
% 26.79/26.99  thf('115', plain,
% 26.79/26.99      (![X20 : $i, X21 : $i, X22 : $i]:
% 26.79/26.99         (~ (r2_hidden @ X20 @ X21)
% 26.79/26.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 26.79/26.99          | (m1_subset_1 @ X20 @ X22))),
% 26.79/26.99      inference('cnf', [status(esa)], [t4_subset])).
% 26.79/26.99  thf('116', plain,
% 26.79/26.99      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 26.79/26.99      inference('sup-', [status(thm)], ['114', '115'])).
% 26.79/26.99  thf('117', plain,
% 26.79/26.99      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_3) @ 
% 26.79/26.99        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 26.79/26.99      inference('sup-', [status(thm)], ['99', '116'])).
% 26.79/26.99  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 26.79/26.99  
% 26.79/26.99  % SZS output end Refutation
% 26.79/26.99  
% 26.79/27.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
