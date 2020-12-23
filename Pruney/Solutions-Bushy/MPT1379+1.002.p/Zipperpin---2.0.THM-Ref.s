%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1379+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.98KqTFBgGz

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:35 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 499 expanded)
%              Number of leaves         :   24 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          : 2314 (9359 expanded)
%              Number of equality atoms :   61 ( 142 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t4_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                  <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( m1_connsp_2 @ C @ A @ B )
                        & ( m1_connsp_2 @ D @ A @ B ) )
                    <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_connsp_2])).

thf('0',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_connsp_2 @ X4 @ X3 @ X2 )
      | ( r2_hidden @ X2 @ ( k1_tops_1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t46_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) )
                = ( k1_tops_1 @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_tops_1 @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X24 ) )
        = ( k1_tops_1 @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( X10
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( X10
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','41','42','43','44','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X3 @ X4 ) )
      | ( m1_connsp_2 @ X4 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_tops_1 @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X24 ) )
        = ( k1_tops_1 @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['82','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','60'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) )
      = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','102','103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X3 @ X4 ) )
      | ( m1_connsp_2 @ X4 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('123',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('125',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_tops_1 @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X24 ) )
        = ( k1_tops_1 @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('135',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('137',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_connsp_2 @ X4 @ X3 @ X2 )
      | ( r2_hidden @ X2 @ ( k1_tops_1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['136','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_connsp_2 @ X4 @ X3 @ X2 )
      | ( r2_hidden @ X2 @ ( k1_tops_1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('161',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['159','161'])).

thf('163',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('165',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['135','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('169',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X3 @ X4 ) )
      | ( m1_connsp_2 @ X4 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('176',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('181',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('182',plain,
    ( ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('185',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','80','123','124','183','184'])).


%------------------------------------------------------------------------------
