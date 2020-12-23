%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1735+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1awEwhY21v

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:09 EST 2020

% Result     : Theorem 7.55s
% Output     : Refutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  225 (1242 expanded)
%              Number of leaves         :   36 ( 384 expanded)
%              Depth                    :   26
%              Number of atoms          : 2159 (18057 expanded)
%              Number of equality atoms :   61 ( 263 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t44_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ C @ B )
               => ( ( v1_tsep_1 @ ( k2_tsep_1 @ A @ C @ B ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ C @ B ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v1_tsep_1 @ C @ A )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ~ ( r1_tsep_1 @ C @ B )
                 => ( ( v1_tsep_1 @ ( k2_tsep_1 @ A @ C @ B ) @ B )
                    & ( m1_pre_topc @ ( k2_tsep_1 @ A @ C @ B ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( r1_tsep_1 @ X29 @ X31 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X30 @ X29 @ X31 ) @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( X8
       != ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( ( u1_struct_0 @ X8 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( u1_struct_0 @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_struct_0 @ sk_C ) )
        = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_struct_0 @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','53','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','55'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','53','54'])).

thf('59',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('62',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( u1_struct_0 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_struct_0 @ sk_B ) )
        = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_struct_0 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','83','84'])).

thf('86',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','83','84'])).

thf('89',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('90',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','60','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','91'])).

thf('93',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('95',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('98',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( X24
       != ( u1_struct_0 @ X22 ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( v1_tsep_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('102',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_tsep_1 @ X22 @ X23 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X22 ) @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_B )
      | ( v1_tsep_1 @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('105',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('107',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_B )
      | ( v1_tsep_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ sk_B )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['99','111'])).

thf('113',plain,
    ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('115',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf(t32_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v3_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('116',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X35 @ ( k2_struct_0 @ X32 ) )
       != X34 )
      | ~ ( v3_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v3_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('117',plain,(
    ! [X32: $i,X33: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X35 @ ( k2_struct_0 @ X32 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X35 @ ( k2_struct_0 @ X32 ) ) @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ sk_B ) @ X0 @ ( k2_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k2_struct_0 @ sk_B ) ) @ sk_B )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('120',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('122',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('129',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('130',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v3_pre_topc @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) @ sk_B )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['118','127','128','131','132','133'])).

thf('135',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C ) ) @ sk_B )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['114','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('138',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('140',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( X24
       != ( u1_struct_0 @ X22 ) )
      | ~ ( v1_tsep_1 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v3_pre_topc @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('141',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X22 ) @ X23 )
      | ~ ( v1_tsep_1 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['139','141'])).

thf('143',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_tsep_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['138','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('150',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v3_pre_topc @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['135','136','137','150','151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['113','152'])).

thf('154',plain,
    ( ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','154'])).

thf('156',plain,
    ( ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ~ ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ~ ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
   <= ~ ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('160',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['157'])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['157'])).

thf('171',plain,(
    ~ ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['158','171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','172'])).

thf('174',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ~ ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['0','186'])).


%------------------------------------------------------------------------------
