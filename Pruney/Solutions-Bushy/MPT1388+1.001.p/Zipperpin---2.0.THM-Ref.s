%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7k86QA3vKb

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  185 (1939 expanded)
%              Number of leaves         :   30 ( 559 expanded)
%              Depth                    :   20
%              Number of atoms          : 1877 (28735 expanded)
%              Number of equality atoms :   43 ( 293 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_connsp_1_type,type,(
    v2_connsp_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_connsp_1_type,type,(
    r3_connsp_1: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_connsp_1_type,type,(
    v3_connsp_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t13_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_connsp_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r3_connsp_1 @ A @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_connsp_1 @ B @ A )
                    & ( r1_tarski @ B @ C ) )
                 => ( r3_connsp_1 @ A @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_connsp_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X2
       != ( k1_pre_topc @ X1 @ X0 ) )
      | ( ( k2_struct_0 @ X2 )
        = X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) @ X1 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      = sk_C_1 )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      = sk_C_1 )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('9',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      = sk_C_1 )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('15',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_connsp_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_connsp_1 @ C @ A )
                    <=> ( v2_connsp_1 @ D @ B ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_connsp_1 @ X19 @ X17 )
      | ( v2_connsp_1 @ X18 @ X16 )
      | ( X19 != X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_connsp_1])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_connsp_1 @ X18 @ X16 )
      | ~ ( v2_connsp_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_connsp_1 @ sk_B @ sk_A )
      | ( v2_connsp_1 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_connsp_1 @ B @ A )
          <=> ( ( v2_connsp_1 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_connsp_1 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_connsp_1 @ X4 @ X5 )
      | ( v2_connsp_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_connsp_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_connsp_1 @ sk_B @ sk_A )
    | ~ ( v3_connsp_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_connsp_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_connsp_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_connsp_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['23','29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_connsp_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v2_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('39',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','37','38','45'])).

thf('47',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('48',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_connsp_1 @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_C @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_connsp_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_connsp_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_connsp_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_connsp_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('53',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('57',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('60',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d6_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r3_connsp_1 @ A @ B @ C )
              <=> ? [D: $i] :
                    ( ( v3_connsp_1 @ D @ ( k1_pre_topc @ A @ B ) )
                    & ( D = C )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_connsp_1 @ X10 @ ( k1_pre_topc @ X8 @ X7 ) )
      | ( X10 != X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X8 @ X7 ) ) ) )
      | ( r3_connsp_1 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_connsp_1])).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r3_connsp_1 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X8 @ X7 ) ) ) )
      | ~ ( v3_connsp_1 @ X9 @ ( k1_pre_topc @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_connsp_1 @ X2 @ ( k1_pre_topc @ X1 @ X0 ) )
      | ( r3_connsp_1 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r3_connsp_1 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r3_connsp_1 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ~ ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( r3_connsp_1 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('71',plain,
    ( ~ ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( r3_connsp_1 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( r3_connsp_1 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['57','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['0','74'])).

thf('76',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('77',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('78',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('80',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ X1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ X1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_connsp_1 @ X4 @ X5 )
      | ~ ( v2_connsp_1 @ X6 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_connsp_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_connsp_1 @ X0 @ sk_A )
      | ~ ( v3_connsp_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v3_connsp_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_connsp_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
    | ( sk_B
      = ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    v2_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','37','38','45'])).

thf('99',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('100',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_connsp_1 @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( sk_C @ X4 @ X5 ) )
      | ( v3_connsp_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_connsp_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_connsp_1 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( v2_connsp_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('105',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['98','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('109',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('111',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A )
    | ( sk_B
      = ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['97','111'])).

thf('113',plain,(
    v2_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','37','38','45'])).

thf('114',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('115',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_connsp_1 @ X4 @ X5 )
      | ( X4
       != ( sk_C @ X4 @ X5 ) )
      | ( v3_connsp_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_connsp_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_connsp_1 @ X1 @ X0 )
      | ( X1
       != ( sk_C @ X1 @ X0 ) )
      | ~ ( v2_connsp_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( X0
       != ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('120',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( X0
       != ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( sk_B
     != ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('124',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( sk_B
     != ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('126',plain,(
    sk_B
 != ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['112','126'])).

thf('128',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['57','73'])).

thf('129',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('130',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_connsp_1 @ X18 @ X16 )
      | ( v2_connsp_1 @ X19 @ X17 )
      | ( X19 != X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_connsp_1])).

thf('131',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_connsp_1 @ X18 @ X17 )
      | ~ ( v2_connsp_1 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ X0 )
      | ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A )
    | ~ ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['128','135'])).

thf('137',plain,(
    v2_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','37','38','45'])).

thf('138',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf('139',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_connsp_1 @ X4 @ X5 )
      | ( v2_connsp_1 @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( v3_connsp_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_connsp_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_connsp_1 @ X1 @ X0 )
      | ( v2_connsp_1 @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ~ ( v2_connsp_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v2_connsp_1 @ ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('144',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( v2_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v2_connsp_1 @ ( sk_C @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v3_connsp_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('148',plain,
    ( ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    | ( v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v3_connsp_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('150',plain,(
    v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('152',plain,(
    v2_connsp_1 @ ( sk_C @ sk_B @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['136','150','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['127','152'])).


%------------------------------------------------------------------------------
