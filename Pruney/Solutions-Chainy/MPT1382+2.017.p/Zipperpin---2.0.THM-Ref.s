%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LorulXWgFj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:52 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 232 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          : 1065 (4263 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t7_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( m1_connsp_2 @ C @ A @ B )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ B )
                            & ( v3_pre_topc @ D @ A )
                            & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_connsp_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X34: $i] :
      ( ~ ( r1_tarski @ X34 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X34 @ sk_A )
      | ~ ( m1_connsp_2 @ X34 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('9',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','12'])).

thf('14',plain,(
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('33',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) )
    | ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(split,[status(esa)],['32'])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 ) ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 ) ) ),
    inference(simpl_trail,[status(thm)],['33','41'])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','53'])).

thf('55',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k1_tops_1 @ X21 @ X20 ) )
      | ( r2_hidden @ X22 @ ( sk_D @ X20 @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k1_tops_1 @ X21 @ X20 ) )
      | ( r1_tarski @ ( sk_D @ X20 @ X22 @ X21 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('87',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['65','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LorulXWgFj
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.85  % Solved by: fo/fo7.sh
% 0.60/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.85  % done 596 iterations in 0.390s
% 0.60/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.85  % SZS output start Refutation
% 0.60/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.85  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.60/0.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.60/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.60/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.85  thf(t7_connsp_2, conjecture,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.60/0.85                    ( ![D:$i]:
% 0.60/0.85                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.60/0.85                          ( m1_subset_1 @
% 0.60/0.85                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.85                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.60/0.85                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.85    (~( ![A:$i]:
% 0.60/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.85            ( l1_pre_topc @ A ) ) =>
% 0.60/0.85          ( ![B:$i]:
% 0.60/0.85            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.85              ( ![C:$i]:
% 0.60/0.85                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.60/0.85                       ( ![D:$i]:
% 0.60/0.85                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.60/0.85                             ( m1_subset_1 @
% 0.60/0.85                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.85                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.60/0.85                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.85    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.60/0.85  thf('0', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(dt_k1_tops_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( l1_pre_topc @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.85       ( m1_subset_1 @
% 0.60/0.85         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.85  thf('1', plain,
% 0.60/0.85      (![X16 : $i, X17 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X16)
% 0.60/0.85          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.60/0.85          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 0.60/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.60/0.85  thf('2', plain,
% 0.60/0.85      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.85  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('4', plain,
% 0.60/0.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.85  thf('5', plain,
% 0.60/0.85      (![X34 : $i]:
% 0.60/0.85         (~ (r1_tarski @ X34 @ sk_C_1)
% 0.60/0.85          | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.60/0.85          | ~ (m1_connsp_2 @ X34 @ sk_A @ sk_B)
% 0.60/0.85          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.85          | (v1_xboole_0 @ X34))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('6', plain,
% 0.60/0.85      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.60/0.85        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.60/0.85        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.85  thf('7', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(fc9_tops_1, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.60/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.85       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.60/0.85  thf('8', plain,
% 0.60/0.85      (![X18 : $i, X19 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X18)
% 0.60/0.85          | ~ (v2_pre_topc @ X18)
% 0.60/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.60/0.85          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 0.60/0.85      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.60/0.85  thf('9', plain,
% 0.60/0.85      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.60/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.85  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('12', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.60/0.85  thf('13', plain,
% 0.60/0.85      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.60/0.85        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.60/0.85      inference('demod', [status(thm)], ['6', '12'])).
% 0.60/0.85  thf('14', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('15', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(d1_connsp_2, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.60/0.85                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('16', plain,
% 0.60/0.85      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.60/0.85          | ~ (m1_connsp_2 @ X30 @ X29 @ X28)
% 0.60/0.85          | (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 0.60/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.60/0.85          | ~ (l1_pre_topc @ X29)
% 0.60/0.85          | ~ (v2_pre_topc @ X29)
% 0.60/0.85          | (v2_struct_0 @ X29))),
% 0.60/0.85      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.60/0.85  thf('17', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.85  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('20', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.60/0.85  thf('21', plain,
% 0.60/0.85      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.60/0.85        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['14', '20'])).
% 0.60/0.85  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('23', plain,
% 0.60/0.85      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['21', '22'])).
% 0.60/0.85  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('25', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.60/0.85      inference('clc', [status(thm)], ['23', '24'])).
% 0.60/0.85  thf('26', plain,
% 0.60/0.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.85  thf('27', plain,
% 0.60/0.85      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.60/0.85          | ~ (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 0.60/0.85          | (m1_connsp_2 @ X30 @ X29 @ X28)
% 0.60/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.60/0.85          | ~ (l1_pre_topc @ X29)
% 0.60/0.85          | ~ (v2_pre_topc @ X29)
% 0.60/0.85          | (v2_struct_0 @ X29))),
% 0.60/0.85      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.60/0.85  thf('28', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X0 @ 
% 0.60/0.85               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.85  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('31', plain,
% 0.60/0.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.85  thf(t55_tops_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( l1_pre_topc @ B ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85               ( ![D:$i]:
% 0.60/0.85                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.60/0.85                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.60/0.85                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.60/0.85                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.60/0.85                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('32', plain,
% 0.60/0.85      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X24)
% 0.60/0.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.60/0.85          | ~ (v3_pre_topc @ X25 @ X24)
% 0.60/0.85          | ((k1_tops_1 @ X24 @ X25) = (X25))
% 0.60/0.85          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.85          | ~ (l1_pre_topc @ X27)
% 0.60/0.85          | ~ (v2_pre_topc @ X27))),
% 0.60/0.85      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.60/0.85  thf('33', plain,
% 0.60/0.85      ((![X24 : $i, X25 : $i]:
% 0.60/0.85          (~ (l1_pre_topc @ X24)
% 0.60/0.85           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.60/0.85           | ~ (v3_pre_topc @ X25 @ X24)
% 0.60/0.85           | ((k1_tops_1 @ X24 @ X25) = (X25))))
% 0.60/0.85         <= ((![X24 : $i, X25 : $i]:
% 0.60/0.85                (~ (l1_pre_topc @ X24)
% 0.60/0.85                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.60/0.85                 | ~ (v3_pre_topc @ X25 @ X24)
% 0.60/0.85                 | ((k1_tops_1 @ X24 @ X25) = (X25)))))),
% 0.60/0.85      inference('split', [status(esa)], ['32'])).
% 0.60/0.85  thf('34', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('35', plain,
% 0.60/0.85      ((![X26 : $i, X27 : $i]:
% 0.60/0.85          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.85           | ~ (l1_pre_topc @ X27)
% 0.60/0.85           | ~ (v2_pre_topc @ X27)))
% 0.60/0.85         <= ((![X26 : $i, X27 : $i]:
% 0.60/0.85                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.85                 | ~ (l1_pre_topc @ X27)
% 0.60/0.85                 | ~ (v2_pre_topc @ X27))))),
% 0.60/0.85      inference('split', [status(esa)], ['32'])).
% 0.60/0.85  thf('36', plain,
% 0.60/0.85      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.60/0.85         <= ((![X26 : $i, X27 : $i]:
% 0.60/0.85                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.85                 | ~ (l1_pre_topc @ X27)
% 0.60/0.85                 | ~ (v2_pre_topc @ X27))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.85  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('39', plain,
% 0.60/0.85      (~
% 0.60/0.85       (![X26 : $i, X27 : $i]:
% 0.60/0.85          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.85           | ~ (l1_pre_topc @ X27)
% 0.60/0.85           | ~ (v2_pre_topc @ X27)))),
% 0.60/0.85      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.60/0.85  thf('40', plain,
% 0.60/0.85      ((![X24 : $i, X25 : $i]:
% 0.60/0.85          (~ (l1_pre_topc @ X24)
% 0.60/0.85           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.60/0.85           | ~ (v3_pre_topc @ X25 @ X24)
% 0.60/0.85           | ((k1_tops_1 @ X24 @ X25) = (X25)))) | 
% 0.60/0.85       (![X26 : $i, X27 : $i]:
% 0.60/0.85          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.60/0.85           | ~ (l1_pre_topc @ X27)
% 0.60/0.85           | ~ (v2_pre_topc @ X27)))),
% 0.60/0.85      inference('split', [status(esa)], ['32'])).
% 0.60/0.85  thf('41', plain,
% 0.60/0.85      ((![X24 : $i, X25 : $i]:
% 0.60/0.85          (~ (l1_pre_topc @ X24)
% 0.60/0.85           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.60/0.85           | ~ (v3_pre_topc @ X25 @ X24)
% 0.60/0.85           | ((k1_tops_1 @ X24 @ X25) = (X25))))),
% 0.60/0.85      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.60/0.85  thf('42', plain,
% 0.60/0.85      (![X24 : $i, X25 : $i]:
% 0.60/0.85         (~ (l1_pre_topc @ X24)
% 0.60/0.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.60/0.85          | ~ (v3_pre_topc @ X25 @ X24)
% 0.60/0.85          | ((k1_tops_1 @ X24 @ X25) = (X25)))),
% 0.60/0.85      inference('simpl_trail', [status(thm)], ['33', '41'])).
% 0.60/0.85  thf('43', plain,
% 0.60/0.85      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85          = (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.60/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['31', '42'])).
% 0.60/0.85  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85          = (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['43', '44'])).
% 0.60/0.85  thf('46', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85         = (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.60/0.85      inference('demod', [status(thm)], ['45', '46'])).
% 0.60/0.85  thf('48', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ sk_A)
% 0.60/0.85          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('demod', [status(thm)], ['28', '29', '30', '47'])).
% 0.60/0.85  thf('49', plain,
% 0.60/0.85      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.60/0.85        | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['25', '48'])).
% 0.60/0.85  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('51', plain,
% 0.60/0.85      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.85  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('53', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 0.60/0.85      inference('clc', [status(thm)], ['51', '52'])).
% 0.60/0.85  thf('54', plain,
% 0.60/0.85      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.60/0.85        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.60/0.85      inference('demod', [status(thm)], ['13', '53'])).
% 0.60/0.85  thf('55', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.60/0.85      inference('clc', [status(thm)], ['23', '24'])).
% 0.60/0.85  thf(d3_tarski, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      (![X1 : $i, X3 : $i]:
% 0.60/0.85         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.85  thf('57', plain,
% 0.60/0.85      (![X1 : $i, X3 : $i]:
% 0.60/0.85         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.85  thf('58', plain,
% 0.60/0.85      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['56', '57'])).
% 0.60/0.85  thf('59', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.60/0.85      inference('simplify', [status(thm)], ['58'])).
% 0.60/0.85  thf(t3_subset, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.85  thf('60', plain,
% 0.60/0.85      (![X7 : $i, X9 : $i]:
% 0.60/0.85         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.60/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.85  thf('61', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.85  thf(t5_subset, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.60/0.85          ( v1_xboole_0 @ C ) ) ))).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.60/0.85         (~ (r2_hidden @ X13 @ X14)
% 0.60/0.85          | ~ (v1_xboole_0 @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.60/0.85      inference('cnf', [status(esa)], [t5_subset])).
% 0.60/0.85  thf('63', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['61', '62'])).
% 0.60/0.85  thf('64', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['55', '63'])).
% 0.60/0.85  thf('65', plain, (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.60/0.85      inference('clc', [status(thm)], ['54', '64'])).
% 0.60/0.85  thf('66', plain,
% 0.60/0.85      (![X1 : $i, X3 : $i]:
% 0.60/0.85         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.85  thf('67', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(t54_tops_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.85       ( ![B:$i,C:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.60/0.85             ( ?[D:$i]:
% 0.60/0.85               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.60/0.85                 ( v3_pre_topc @ D @ A ) & 
% 0.60/0.85                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('68', plain,
% 0.60/0.85      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.85          | ~ (r2_hidden @ X22 @ (k1_tops_1 @ X21 @ X20))
% 0.60/0.85          | (r2_hidden @ X22 @ (sk_D @ X20 @ X22 @ X21))
% 0.60/0.85          | ~ (l1_pre_topc @ X21)
% 0.60/0.85          | ~ (v2_pre_topc @ X21))),
% 0.60/0.85      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.60/0.85  thf('69', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (r2_hidden @ X0 @ (sk_D @ sk_C_1 @ X0 @ sk_A))
% 0.60/0.85          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.85  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('72', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r2_hidden @ X0 @ (sk_D @ sk_C_1 @ X0 @ sk_A))
% 0.60/0.85          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.60/0.85      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.60/0.85  thf('73', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.60/0.85          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.60/0.85             (sk_D @ sk_C_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_A)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['66', '72'])).
% 0.60/0.85  thf('74', plain,
% 0.60/0.85      (![X1 : $i, X3 : $i]:
% 0.60/0.85         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.85  thf('75', plain,
% 0.60/0.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('76', plain,
% 0.60/0.85      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.85          | ~ (r2_hidden @ X22 @ (k1_tops_1 @ X21 @ X20))
% 0.60/0.85          | (r1_tarski @ (sk_D @ X20 @ X22 @ X21) @ X20)
% 0.60/0.85          | ~ (l1_pre_topc @ X21)
% 0.60/0.85          | ~ (v2_pre_topc @ X21))),
% 0.60/0.85      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.60/0.85  thf('77', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (v2_pre_topc @ sk_A)
% 0.60/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.85          | (r1_tarski @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_C_1)
% 0.60/0.85          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['75', '76'])).
% 0.60/0.85  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('80', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r1_tarski @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_C_1)
% 0.60/0.85          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.60/0.85      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.60/0.85  thf('81', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.60/0.85          | (r1_tarski @ 
% 0.60/0.85             (sk_D @ sk_C_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_A) @ 
% 0.60/0.85             sk_C_1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['74', '80'])).
% 0.60/0.85  thf('82', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.85          | (r2_hidden @ X0 @ X2)
% 0.60/0.85          | ~ (r1_tarski @ X1 @ X2))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.85  thf('83', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.60/0.85          | (r2_hidden @ X1 @ sk_C_1)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ 
% 0.60/0.85               (sk_D @ sk_C_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.60/0.85                sk_A)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['81', '82'])).
% 0.60/0.85  thf('84', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.60/0.85          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1)
% 0.60/0.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['73', '83'])).
% 0.60/0.85  thf('85', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1)
% 0.60/0.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 0.60/0.85      inference('simplify', [status(thm)], ['84'])).
% 0.60/0.85  thf('86', plain,
% 0.60/0.85      (![X1 : $i, X3 : $i]:
% 0.60/0.85         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.85  thf('87', plain,
% 0.60/0.85      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.60/0.85        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.60/0.85      inference('sup-', [status(thm)], ['85', '86'])).
% 0.60/0.85  thf('88', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.60/0.85      inference('simplify', [status(thm)], ['87'])).
% 0.60/0.85  thf('89', plain, ($false), inference('demod', [status(thm)], ['65', '88'])).
% 0.60/0.85  
% 0.60/0.85  % SZS output end Refutation
% 0.60/0.85  
% 0.60/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
