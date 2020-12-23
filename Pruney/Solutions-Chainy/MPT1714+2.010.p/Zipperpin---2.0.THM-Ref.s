%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5YM8ciKJy

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 (1046 expanded)
%              Number of leaves         :   35 ( 320 expanded)
%              Depth                    :   23
%              Number of atoms          :  949 (13971 expanded)
%              Number of equality atoms :   14 (  70 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X36 )
      | ( r1_tsep_1 @ X36 @ X35 )
      | ~ ( r1_tsep_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('7',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('13',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','14','21'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X30 )
      | ~ ( r1_tsep_1 @ X31 @ X30 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('24',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('27',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['3','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['2','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X30 )
      | ~ ( r1_tsep_1 @ X31 @ X30 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('37',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('39',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('40',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','64'])).

thf('66',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X30 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ( r1_tsep_1 @ X31 @ X30 )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_tsep_1 @ sk_D_2 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('72',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('75',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','73','74'])).

thf('76',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X36 )
      | ( r1_tsep_1 @ X36 @ X35 )
      | ~ ( r1_tsep_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('77',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('79',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('80',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','73','74'])).

thf('84',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('88',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['82','85','86','87'])).

thf('89',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['33','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('91',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X30 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ( r1_tsep_1 @ X31 @ X30 )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('101',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('102',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X36 )
      | ( r1_tsep_1 @ X36 @ X35 )
      | ~ ( r1_tsep_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('106',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('107',plain,(
    r1_tsep_1 @ sk_B @ sk_D_2 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( $false
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['1','107'])).

thf('109',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['108','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5YM8ciKJy
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 238 iterations in 0.121s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.58  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.58  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(t23_tmap_1, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.58           ( ![C:$i]:
% 0.20/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.58               ( ![D:$i]:
% 0.20/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.58                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.58                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.58                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.58                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.58            ( l1_pre_topc @ A ) ) =>
% 0.20/0.58          ( ![B:$i]:
% 0.20/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.58              ( ![C:$i]:
% 0.20/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.58                  ( ![D:$i]:
% 0.20/0.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.58                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.58                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.58                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.58                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf(d3_struct_0, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X12 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X12 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('split', [status(esa)], ['4'])).
% 0.20/0.58  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.58       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X35 : $i, X36 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X35)
% 0.20/0.58          | ~ (l1_struct_0 @ X36)
% 0.20/0.58          | (r1_tsep_1 @ X36 @ X35)
% 0.20/0.58          | ~ (r1_tsep_1 @ X35 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.20/0.58         | ~ (l1_struct_0 @ sk_D_2)
% 0.20/0.58         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('8', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(dt_m1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X24 : $i, X25 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.58          | (l1_pre_topc @ X24)
% 0.20/0.58          | ~ (l1_pre_topc @ X25))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.58  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.20/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('12', plain, ((l1_pre_topc @ sk_D_2)),
% 0.20/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf(dt_l1_pre_topc, axiom,
% 0.20/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('14', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('15', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X24 : $i, X25 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.58          | (l1_pre_topc @ X24)
% 0.20/0.58          | ~ (l1_pre_topc @ X25))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.58  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('19', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('21', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['7', '14', '21'])).
% 0.20/0.58  thf(d3_tsep_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_struct_0 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( l1_struct_0 @ B ) =>
% 0.20/0.58           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.58             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X30)
% 0.20/0.58          | ~ (r1_tsep_1 @ X31 @ X30)
% 0.20/0.58          | (r1_xboole_0 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.20/0.58          | ~ (l1_struct_0 @ X31))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (((~ (l1_struct_0 @ sk_D_2)
% 0.20/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('26', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '27'])).
% 0.20/0.58  thf('29', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['2', '30'])).
% 0.20/0.58  thf('32', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.20/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X12 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('split', [status(esa)], ['4'])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X30)
% 0.20/0.58          | ~ (r1_tsep_1 @ X31 @ X30)
% 0.20/0.58          | (r1_xboole_0 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.20/0.58          | ~ (l1_struct_0 @ X31))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (((~ (l1_struct_0 @ sk_D_2)
% 0.20/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('38', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('39', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.58         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['34', '40'])).
% 0.20/0.58  thf('42', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.20/0.58         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.58  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(d9_pre_topc, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( l1_pre_topc @ B ) =>
% 0.20/0.58           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.58             ( ( ![C:$i]:
% 0.20/0.58                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.58                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.58                     ( ?[D:$i]:
% 0.20/0.58                       ( ( m1_subset_1 @
% 0.20/0.58                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.58                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.58                         ( ( C ) =
% 0.20/0.58                           ( k9_subset_1 @
% 0.20/0.58                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.20/0.58               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_2, axiom,
% 0.20/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.58       ( ( ( C ) =
% 0.20/0.58           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.20/0.58         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_3, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_pre_topc @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( l1_pre_topc @ B ) =>
% 0.20/0.58           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.58             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.20/0.58               ( ![C:$i]:
% 0.20/0.58                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.58                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.58                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X18 : $i, X19 : $i]:
% 0.20/0.58         (~ (l1_pre_topc @ X18)
% 0.20/0.58          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.58          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 0.20/0.58          | ~ (l1_pre_topc @ X19))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      ((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.58        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.20/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.58  thf('47', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf('48', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X24 : $i, X25 : $i]:
% 0.20/0.58         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.58          | (l1_pre_topc @ X24)
% 0.20/0.58          | ~ (l1_pre_topc @ X25))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.58  thf('50', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.58  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['46', '47', '52'])).
% 0.20/0.58  thf(d10_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.58  thf(t8_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.58       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X9 @ X10)
% 0.20/0.58          | ~ (r1_tarski @ X11 @ X10)
% 0.20/0.58          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 0.20/0.58      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      ((r1_tarski @ 
% 0.20/0.58        (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)) @ 
% 0.20/0.58        (k2_struct_0 @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['53', '57'])).
% 0.20/0.58  thf(t7_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      (![X0 : $i, X2 : $i]:
% 0.20/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.58          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (((k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 0.20/0.58         = (k2_struct_0 @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['58', '61'])).
% 0.20/0.58  thf(t70_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.58            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.58       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.58            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.58         ((r1_xboole_0 @ X3 @ X6)
% 0.20/0.58          | ~ (r1_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X6)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.58  thf('64', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.58          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.20/0.58         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['43', '64'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      (![X12 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X30)
% 0.20/0.58          | ~ (r1_xboole_0 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.20/0.58          | (r1_tsep_1 @ X31 @ X30)
% 0.20/0.58          | ~ (l1_struct_0 @ X31))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X1)
% 0.20/0.58          | (r1_tsep_1 @ X1 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.58  thf('69', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((r1_tsep_1 @ X1 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X1)
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | ~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.58  thf('70', plain,
% 0.20/0.58      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.58         | ~ (l1_struct_0 @ sk_D_2)
% 0.20/0.58         | (r1_tsep_1 @ sk_D_2 @ sk_B))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['65', '69'])).
% 0.20/0.58  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.58  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.58  thf('74', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['70', '73', '74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (![X35 : $i, X36 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X35)
% 0.20/0.58          | ~ (l1_struct_0 @ X36)
% 0.20/0.58          | (r1_tsep_1 @ X36 @ X35)
% 0.20/0.58          | ~ (r1_tsep_1 @ X35 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.20/0.58         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.58         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.58  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.58  thf('79', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('80', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.58  thf('81', plain,
% 0.20/0.58      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('82', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['70', '73', '74'])).
% 0.20/0.58  thf('84', plain,
% 0.20/0.58      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('87', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.20/0.58      inference('split', [status(esa)], ['4'])).
% 0.20/0.58  thf('88', plain, (((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['82', '85', '86', '87'])).
% 0.20/0.58  thf('89', plain,
% 0.20/0.58      ((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['33', '88'])).
% 0.20/0.58  thf('90', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.58          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.58  thf('91', plain,
% 0.20/0.58      ((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.58  thf('92', plain,
% 0.20/0.58      (![X12 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('93', plain,
% 0.20/0.58      (![X12 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('94', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X30)
% 0.20/0.58          | ~ (r1_xboole_0 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 0.20/0.58          | (r1_tsep_1 @ X31 @ X30)
% 0.20/0.58          | ~ (l1_struct_0 @ X31))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.58  thf('95', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | (r1_tsep_1 @ X0 @ X1)
% 0.20/0.58          | ~ (l1_struct_0 @ X1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.58  thf('96', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X1)
% 0.20/0.58          | (r1_tsep_1 @ X0 @ X1)
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['95'])).
% 0.20/0.58  thf('97', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_xboole_0 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X1)
% 0.20/0.58          | (r1_tsep_1 @ X1 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['92', '96'])).
% 0.20/0.58  thf('98', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((r1_tsep_1 @ X1 @ X0)
% 0.20/0.58          | ~ (l1_struct_0 @ X1)
% 0.20/0.58          | ~ (l1_struct_0 @ X0)
% 0.20/0.58          | ~ (r1_xboole_0 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['97'])).
% 0.20/0.58  thf('99', plain,
% 0.20/0.58      ((~ (l1_struct_0 @ sk_B)
% 0.20/0.58        | ~ (l1_struct_0 @ sk_D_2)
% 0.20/0.58        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['91', '98'])).
% 0.20/0.58  thf('100', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.58  thf('101', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('102', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.20/0.58      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.58  thf('103', plain,
% 0.20/0.58      (![X35 : $i, X36 : $i]:
% 0.20/0.58         (~ (l1_struct_0 @ X35)
% 0.20/0.58          | ~ (l1_struct_0 @ X36)
% 0.20/0.58          | (r1_tsep_1 @ X36 @ X35)
% 0.20/0.58          | ~ (r1_tsep_1 @ X35 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.58  thf('104', plain,
% 0.20/0.58      (((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.20/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.58        | ~ (l1_struct_0 @ sk_D_2))),
% 0.20/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.58  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.58  thf('106', plain, ((l1_struct_0 @ sk_D_2)),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('107', plain, ((r1_tsep_1 @ sk_B @ sk_D_2)),
% 0.20/0.58      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.20/0.58  thf('108', plain, (($false) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.20/0.58      inference('demod', [status(thm)], ['1', '107'])).
% 0.20/0.58  thf('109', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.20/0.58      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.58  thf('110', plain,
% 0.20/0.58      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('111', plain, (((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.58  thf('112', plain,
% 0.20/0.58      (~ ((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.20/0.58      inference('split', [status(esa)], ['0'])).
% 0.20/0.58  thf('113', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['111', '112'])).
% 0.20/0.58  thf('114', plain, ($false),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['108', '113'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
