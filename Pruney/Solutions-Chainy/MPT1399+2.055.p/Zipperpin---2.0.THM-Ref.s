%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fVUYtsX2ve

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 288 expanded)
%              Number of leaves         :   41 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :  820 (3883 expanded)
%              Number of equality atoms :   46 ( 159 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('2',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X25: $i] :
      ( ( X25 = sk_C )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('8',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('12',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ( r2_hidden @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('15',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ( r2_hidden @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( X13 = sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ sk_C ) )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = ( k5_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ sk_C )
      = X4 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = X0 ) ),
    inference(demod,[status(thm)],['20','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B_2 @ sk_C )
    | ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('35',plain,(
    ! [X25: $i] :
      ( ( X25 = sk_C )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = sk_C )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_C )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_C )
    | ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','53'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('55',plain,(
    ! [X33: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X33 ) @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('56',plain,(
    ! [X34: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('57',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('58',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ! [X36: $i] :
      ( ~ ( v3_pre_topc @ X36 @ sk_A )
      | ~ ( v4_pre_topc @ X36 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X36 )
      | ( r2_hidden @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('69',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ( r2_hidden @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['54','73'])).

thf('75',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_B_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['3','87'])).

thf('89',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fVUYtsX2ve
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 341 iterations in 0.215s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.65  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(t28_connsp_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @
% 0.45/0.65                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65               ( ~( ( ![D:$i]:
% 0.45/0.65                      ( ( m1_subset_1 @
% 0.45/0.65                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                        ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65                          ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.65                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.65                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65            ( l1_pre_topc @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65              ( ![C:$i]:
% 0.45/0.65                ( ( m1_subset_1 @
% 0.45/0.65                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65                  ( ~( ( ![D:$i]:
% 0.45/0.65                         ( ( m1_subset_1 @
% 0.45/0.65                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                           ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65                             ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.65                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.65                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.45/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t6_mcart_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.65                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.65                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.45/0.65                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.45/0.65                       ( r2_hidden @ G @ B ) ) =>
% 0.45/0.65                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X25 : $i]:
% 0.45/0.65         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.45/0.65      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.65  thf('2', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X25 : $i]: (((X25) = (sk_C)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.45/0.65      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf(d3_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X31 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('5', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_l1_pre_topc, axiom,
% 0.45/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.65  thf('8', plain, (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.65  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain, ((m1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.65  thf(t4_subset_1, axiom,
% 0.45/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.65  thf('12', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('13', plain, (![X11 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X11))),
% 0.45/0.65      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf(t50_subset_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @ C @ A ) =>
% 0.45/0.65               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.45/0.65                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.45/0.65          | (r2_hidden @ X14 @ X12)
% 0.45/0.65          | (r2_hidden @ X14 @ (k3_subset_1 @ X13 @ X12))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ X13)
% 0.45/0.65          | ((X13) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.45/0.65  thf('15', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.45/0.65          | (r2_hidden @ X14 @ X12)
% 0.45/0.65          | (r2_hidden @ X14 @ (k3_subset_1 @ X13 @ X12))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ X13)
% 0.45/0.65          | ((X13) = (sk_C)))),
% 0.45/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (sk_C))
% 0.45/0.65          | ~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.65          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ sk_C))
% 0.45/0.65          | (r2_hidden @ X1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.65  thf('18', plain, (![X11 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X11))),
% 0.45/0.65      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf(d5_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.65       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]:
% 0.45/0.65         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 0.45/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf(t2_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('22', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('23', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('24', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf(t100_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (k5_xboole_0 @ X0 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('27', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('28', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('29', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ sk_C) = (X4))),
% 0.45/0.65      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['26', '29'])).
% 0.45/0.65  thf('31', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['20', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (sk_C))
% 0.45/0.65          | ~ (m1_subset_1 @ X1 @ X0)
% 0.45/0.65          | (r2_hidden @ X1 @ X0)
% 0.45/0.65          | (r2_hidden @ X1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['17', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (((r2_hidden @ sk_B_2 @ sk_C)
% 0.45/0.65        | (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | ((k2_struct_0 @ sk_A) = (sk_C)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '32'])).
% 0.45/0.65  thf('34', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X25 : $i]: (((X25) = (sk_C)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.45/0.65      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf(dt_k2_subset_1, axiom,
% 0.45/0.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.65  thf('37', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.65  thf('38', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.45/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf(t5_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X20 @ X21)
% 0.45/0.65          | ~ (v1_xboole_0 @ X22)
% 0.45/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('41', plain, (![X0 : $i]: (((X0) = (sk_C)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['35', '40'])).
% 0.45/0.65  thf('42', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X1 @ X0) = (sk_C)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.65  thf('44', plain, (![X11 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X11))),
% 0.45/0.65      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X20 @ X21)
% 0.45/0.65          | ~ (v1_xboole_0 @ X22)
% 0.45/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | ~ (v1_xboole_0 @ X0)
% 0.45/0.65          | ~ (v1_xboole_0 @ X3))),
% 0.45/0.65      inference('sup-', [status(thm)], ['43', '46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('condensation', [status(thm)], ['47'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X1 : $i]: (~ (r2_hidden @ X1 @ sk_C) | ~ (v1_xboole_0 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['34', '48'])).
% 0.45/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.65  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.65  thf('51', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('52', plain, ((v1_xboole_0 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('53', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['49', '52'])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((((k2_struct_0 @ sk_A) = (sk_C))
% 0.45/0.65        | (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['33', '53'])).
% 0.45/0.65  thf(fc4_pre_topc, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X33 : $i]:
% 0.45/0.65         ((v4_pre_topc @ (k2_struct_0 @ X33) @ X33)
% 0.45/0.65          | ~ (l1_pre_topc @ X33)
% 0.45/0.65          | ~ (v2_pre_topc @ X33))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.45/0.65  thf(fc10_tops_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (![X34 : $i]:
% 0.45/0.65         ((v3_pre_topc @ (k2_struct_0 @ X34) @ X34)
% 0.45/0.65          | ~ (l1_pre_topc @ X34)
% 0.45/0.65          | ~ (v2_pre_topc @ X34))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.45/0.65  thf('57', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.45/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X31 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X36 : $i]:
% 0.45/0.65         (~ (v3_pre_topc @ X36 @ sk_A)
% 0.45/0.65          | ~ (v4_pre_topc @ X36 @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ sk_B_2 @ X36)
% 0.45/0.65          | (r2_hidden @ X36 @ sk_C)
% 0.45/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.65          | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65          | (r2_hidden @ X0 @ sk_C)
% 0.45/0.65          | ~ (r2_hidden @ sk_B_2 @ X0)
% 0.45/0.65          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.45/0.65          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.65  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.45/0.65          | (r2_hidden @ X0 @ sk_C)
% 0.45/0.65          | ~ (r2_hidden @ sk_B_2 @ X0)
% 0.45/0.65          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.45/0.65          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (k2_struct_0 @ sk_A) @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['57', '62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ (k2_struct_0 @ sk_A) @ sk_C)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['56', '63'])).
% 0.45/0.65  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (((r2_hidden @ (k2_struct_0 @ sk_A) @ sk_C)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.45/0.65  thf('68', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['49', '52'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['55', '69'])).
% 0.45/0.65  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('73', plain, (~ (r2_hidden @ sk_B_2 @ (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.45/0.65  thf('74', plain, (((k2_struct_0 @ sk_A) = (sk_C))),
% 0.45/0.65      inference('clc', [status(thm)], ['54', '73'])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (![X31 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(rc3_tops_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ?[B:$i]:
% 0.45/0.65         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.45/0.65           ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.65           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      (![X35 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (sk_B_1 @ X35) @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.45/0.65          | ~ (l1_pre_topc @ X35)
% 0.45/0.65          | ~ (v2_pre_topc @ X35)
% 0.45/0.65          | (v2_struct_0 @ X35))),
% 0.45/0.65      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X20 @ X21)
% 0.45/0.65          | ~ (v1_xboole_0 @ X22)
% 0.45/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v2_struct_0 @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.65          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.65          | ~ (l1_struct_0 @ X0)
% 0.45/0.65          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0))
% 0.45/0.65          | ~ (l1_pre_topc @ X0)
% 0.45/0.65          | ~ (v2_pre_topc @ X0)
% 0.45/0.65          | (v2_struct_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['75', '78'])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ sk_C)
% 0.45/0.65          | (v2_struct_0 @ sk_A)
% 0.45/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.45/0.65          | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['74', '79'])).
% 0.45/0.65  thf('81', plain, ((v1_xboole_0 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_struct_0 @ sk_A) | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.45/0.65  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('87', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['85', '86'])).
% 0.45/0.65  thf('88', plain, (((sk_B_1 @ sk_A) = (sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '87'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (![X35 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (sk_B_1 @ X35))
% 0.45/0.65          | ~ (l1_pre_topc @ X35)
% 0.45/0.65          | ~ (v2_pre_topc @ X35)
% 0.45/0.65          | (v2_struct_0 @ X35))),
% 0.45/0.65      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ sk_C)
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.65  thf('91', plain, ((v1_xboole_0 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('94', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.45/0.65  thf('95', plain, ($false), inference('demod', [status(thm)], ['0', '94'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
