%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1271+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oyHTZXksYu

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:22 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 197 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  912 (3104 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t90_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_tops_1 @ B @ A )
                  & ( v3_tops_1 @ C @ A ) )
               => ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_tops_1 @ B @ A )
                    & ( v3_tops_1 @ C @ A ) )
                 => ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t90_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ( v3_tops_1 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t85_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tops_1 @ B @ A )
                  & ( v2_tops_1 @ C @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ X18 @ X19 )
      | ~ ( v2_tops_1 @ X20 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t85_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_tops_1 @ X3 @ X4 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','36'])).

thf('38',plain,
    ( ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_tops_1 @ X3 @ X4 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('47',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['38','44','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v2_tops_1 @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k2_pre_topc @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k4_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ X15 ) @ ( k2_pre_topc @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('69',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['57','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['16','70'])).


%------------------------------------------------------------------------------
