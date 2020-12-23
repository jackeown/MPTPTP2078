%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZwqY24GLok

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 541 expanded)
%              Number of leaves         :   25 ( 166 expanded)
%              Depth                    :   27
%              Number of atoms          :  878 (7357 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t23_tmap_1,conjecture,(
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
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) )
                      | ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) )
                        | ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tmap_1])).

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('9',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('30',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('37',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['2','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('49',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('52',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('55',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('67',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('73',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('75',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('78',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['61','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('85',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('87',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['60','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('90',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['59','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('93',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['56'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('97',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['56'])).

thf('98',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['56'])).

thf('100',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('101',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('103',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('104',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('107',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('110',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('112',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['58','95','98','99','112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZwqY24GLok
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 89 iterations in 0.033s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.49  thf(dt_l1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.49  thf('0', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('1', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('2', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('3', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('4', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('5', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf(t23_tmap_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.19/0.49                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.19/0.49                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.19/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.49            ( l1_pre_topc @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.49                  ( ![D:$i]:
% 0.19/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.19/0.49                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.19/0.49                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.19/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.19/0.49  thf('6', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['6'])).
% 0.19/0.49  thf(d3_tsep_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( l1_struct_0 @ B ) =>
% 0.19/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.19/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.19/0.49  thf('11', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_m1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.49          | (l1_pre_topc @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('15', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '16'])).
% 0.19/0.49  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.49          | (l1_pre_topc @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['17', '22'])).
% 0.19/0.49  thf(t83_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.19/0.49          = (u1_struct_0 @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t1_tsep_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.49           ( m1_subset_1 @
% 0.19/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X16 @ X17)
% 0.19/0.49          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.49          | ~ (l1_pre_topc @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_C)
% 0.19/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf(t85_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X3 @ X4)
% 0.19/0.49          | (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.49          (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['25', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '37'])).
% 0.19/0.49  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.49          | (l1_pre_topc @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.49  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '44'])).
% 0.19/0.49  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.19/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X15)
% 0.19/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '49'])).
% 0.19/0.49  thf('51', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '52'])).
% 0.19/0.49  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['56'])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['55', '57'])).
% 0.19/0.49  thf('59', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('60', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('61', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('62', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('63', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('64', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('65', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['6'])).
% 0.19/0.49  thf('66', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X15)
% 0.19/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.49  thf('67', plain,
% 0.19/0.49      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.49  thf('68', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['64', '67'])).
% 0.19/0.49  thf('69', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('70', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['68', '69'])).
% 0.19/0.49  thf('71', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['63', '70'])).
% 0.19/0.49  thf('72', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('73', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['71', '72'])).
% 0.19/0.49  thf('74', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('75', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.19/0.49  thf('76', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['62', '75'])).
% 0.19/0.49  thf('77', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('78', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.49  thf('79', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['61', '78'])).
% 0.19/0.49  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('81', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.49  thf('82', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.49  thf('83', plain,
% 0.19/0.49      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.19/0.49          = (u1_struct_0 @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['81', '82'])).
% 0.19/0.49  thf('84', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.49          (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('85', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['83', '84'])).
% 0.19/0.49  thf('86', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('87', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['85', '86'])).
% 0.19/0.49  thf('88', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['60', '87'])).
% 0.19/0.49  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('90', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['88', '89'])).
% 0.19/0.49  thf('91', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['59', '90'])).
% 0.19/0.49  thf('92', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('93', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['91', '92'])).
% 0.19/0.49  thf('94', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['56'])).
% 0.19/0.49  thf('95', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['93', '94'])).
% 0.19/0.49  thf('96', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.49  thf('97', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['56'])).
% 0.19/0.49  thf('98', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['96', '97'])).
% 0.19/0.49  thf('99', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('split', [status(esa)], ['56'])).
% 0.19/0.49  thf('100', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('101', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('102', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['91', '92'])).
% 0.19/0.49  thf('103', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X15)
% 0.19/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.49  thf('104', plain,
% 0.19/0.49      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['102', '103'])).
% 0.19/0.49  thf('105', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['101', '104'])).
% 0.19/0.49  thf('106', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('107', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['105', '106'])).
% 0.19/0.49  thf('108', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['100', '107'])).
% 0.19/0.49  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('110', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['108', '109'])).
% 0.19/0.49  thf('111', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['56'])).
% 0.19/0.49  thf('112', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['110', '111'])).
% 0.19/0.49  thf('113', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.19/0.49      inference('split', [status(esa)], ['6'])).
% 0.19/0.49  thf('114', plain, ($false),
% 0.19/0.49      inference('sat_resolution*', [status(thm)],
% 0.19/0.49                ['58', '95', '98', '99', '112', '113'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
