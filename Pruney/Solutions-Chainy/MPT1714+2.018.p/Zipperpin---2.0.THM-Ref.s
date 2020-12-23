%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IERKiWgJgo

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 818 expanded)
%              Number of leaves         :   35 ( 255 expanded)
%              Depth                    :   17
%              Number of atoms          :  907 (11369 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
    | ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( r1_tsep_1 @ X27 @ X26 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('4',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_3 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_D_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_D_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['4','11','18'])).

thf('20',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( k2_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( k2_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_C_2 ),
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

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['25','26','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_struct_0 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_struct_0 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('54',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('57',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['52','55','56'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X29 )
      | ( r1_tsep_1 @ X29 @ X28 )
      | ~ ( r1_tsep_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('59',plain,
    ( ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('62',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_3 )
    | ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
    | ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(split,[status(esa)],['1'])).

thf('68',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X29 )
      | ( r1_tsep_1 @ X29 @ X28 )
      | ~ ( r1_tsep_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('69',plain,
    ( ( ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('71',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('72',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( r1_tsep_1 @ X27 @ X26 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('74',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_3 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('76',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( k2_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('80',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_3 ) @ ( k2_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('82',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('84',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('86',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('87',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['63'])).

thf('89',plain,
    ( ~ ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
    | ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['63'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
    | ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['63'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('95',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X29 )
      | ( r1_tsep_1 @ X29 @ X28 )
      | ~ ( r1_tsep_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('96',plain,
    ( ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('99',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('101',plain,
    ( ~ ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
    | ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
    | ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('103',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['65','89','92','93','101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IERKiWgJgo
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.60  % Solved by: fo/fo7.sh
% 0.20/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.60  % done 346 iterations in 0.140s
% 0.20/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.60  % SZS output start Refutation
% 0.20/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.60  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.60  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.60  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.60  thf(d3_struct_0, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.60  thf('0', plain,
% 0.20/0.60      (![X12 : $i]:
% 0.20/0.60         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.60  thf(t23_tmap_1, conjecture,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.60           ( ![C:$i]:
% 0.20/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.60               ( ![D:$i]:
% 0.20/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.60                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.60                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.60                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.60                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.60    (~( ![A:$i]:
% 0.20/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.60            ( l1_pre_topc @ A ) ) =>
% 0.20/0.60          ( ![B:$i]:
% 0.20/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.60              ( ![C:$i]:
% 0.20/0.60                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.60                  ( ![D:$i]:
% 0.20/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.60                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.60                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.60                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.60                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.60    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.20/0.60  thf('1', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_C_2 @ sk_D_3) | (r1_tsep_1 @ sk_D_3 @ sk_C_2))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('2', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_D_3 @ sk_C_2)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('split', [status(esa)], ['1'])).
% 0.20/0.60  thf(d3_tsep_1, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_struct_0 @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( l1_struct_0 @ B ) =>
% 0.20/0.60           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.60             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.60  thf('3', plain,
% 0.20/0.60      (![X26 : $i, X27 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X26)
% 0.20/0.60          | ~ (r1_tsep_1 @ X27 @ X26)
% 0.20/0.60          | (r1_xboole_0 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.20/0.60          | ~ (l1_struct_0 @ X27))),
% 0.20/0.60      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.60  thf('4', plain,
% 0.20/0.60      (((~ (l1_struct_0 @ sk_D_3)
% 0.20/0.60         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (u1_struct_0 @ sk_C_2))
% 0.20/0.60         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.60  thf('5', plain, ((m1_pre_topc @ sk_D_3 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(dt_m1_pre_topc, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_pre_topc @ A ) =>
% 0.20/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.60  thf('6', plain,
% 0.20/0.60      (![X24 : $i, X25 : $i]:
% 0.20/0.60         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.60          | (l1_pre_topc @ X24)
% 0.20/0.60          | ~ (l1_pre_topc @ X25))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.60  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_3))),
% 0.20/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.60  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('9', plain, ((l1_pre_topc @ sk_D_3)),
% 0.20/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.60  thf(dt_l1_pre_topc, axiom,
% 0.20/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.60  thf('10', plain,
% 0.20/0.60      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.60  thf('11', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('12', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('13', plain,
% 0.20/0.60      (![X24 : $i, X25 : $i]:
% 0.20/0.60         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.60          | (l1_pre_topc @ X24)
% 0.20/0.60          | ~ (l1_pre_topc @ X25))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.60  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.20/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.60  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('16', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.60  thf('17', plain,
% 0.20/0.60      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.60  thf('18', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.60  thf('19', plain,
% 0.20/0.60      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (u1_struct_0 @ sk_C_2)))
% 0.20/0.60         <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('demod', [status(thm)], ['4', '11', '18'])).
% 0.20/0.60  thf('20', plain,
% 0.20/0.60      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['0', '19'])).
% 0.20/0.60  thf('21', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.60  thf('22', plain,
% 0.20/0.60      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (k2_struct_0 @ sk_C_2)))
% 0.20/0.60         <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.60  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_C_2)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(d9_pre_topc, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_pre_topc @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( l1_pre_topc @ B ) =>
% 0.20/0.60           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.60             ( ( ![C:$i]:
% 0.20/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.60                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.60                     ( ?[D:$i]:
% 0.20/0.60                       ( ( m1_subset_1 @
% 0.20/0.60                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.60                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.60                         ( ( C ) =
% 0.20/0.60                           ( k9_subset_1 @
% 0.20/0.60                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.20/0.60               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.60  thf(zf_stmt_2, axiom,
% 0.20/0.60    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.60     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.60       ( ( ( C ) =
% 0.20/0.60           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.20/0.60         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.60  thf(zf_stmt_3, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_pre_topc @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( l1_pre_topc @ B ) =>
% 0.20/0.60           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.60             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.20/0.60               ( ![C:$i]:
% 0.20/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.60                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.60                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf('24', plain,
% 0.20/0.60      (![X18 : $i, X19 : $i]:
% 0.20/0.60         (~ (l1_pre_topc @ X18)
% 0.20/0.60          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.60          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 0.20/0.60          | ~ (l1_pre_topc @ X19))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.60  thf('25', plain,
% 0.20/0.60      ((~ (l1_pre_topc @ sk_C_2)
% 0.20/0.60        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.60  thf('26', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.60  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('28', plain,
% 0.20/0.60      (![X24 : $i, X25 : $i]:
% 0.20/0.60         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.60          | (l1_pre_topc @ X24)
% 0.20/0.60          | ~ (l1_pre_topc @ X25))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.60  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.60  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.60  thf('32', plain,
% 0.20/0.60      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))),
% 0.20/0.60      inference('demod', [status(thm)], ['25', '26', '31'])).
% 0.20/0.60  thf(t28_xboole_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.60  thf('33', plain,
% 0.20/0.60      (![X10 : $i, X11 : $i]:
% 0.20/0.60         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.60  thf('34', plain,
% 0.20/0.60      (((k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60         = (k2_struct_0 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.60  thf(t3_xboole_0, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.60  thf('35', plain,
% 0.20/0.60      (![X6 : $i, X7 : $i]:
% 0.20/0.60         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.60  thf(d4_xboole_0, axiom,
% 0.20/0.60    (![A:$i,B:$i,C:$i]:
% 0.20/0.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.60       ( ![D:$i]:
% 0.20/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.60  thf('36', plain,
% 0.20/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.60          | (r2_hidden @ X4 @ X2)
% 0.20/0.60          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.60  thf('37', plain,
% 0.20/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.60         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.60  thf('38', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.20/0.60          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.20/0.60      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.60  thf('39', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((r2_hidden @ (sk_C @ X0 @ (k2_struct_0 @ sk_B)) @ 
% 0.20/0.60           (k2_struct_0 @ sk_C_2))
% 0.20/0.60          | (r1_xboole_0 @ 
% 0.20/0.60             (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2)) @ X0))),
% 0.20/0.60      inference('sup+', [status(thm)], ['34', '38'])).
% 0.20/0.60  thf('40', plain,
% 0.20/0.60      (((k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60         = (k2_struct_0 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.60  thf('41', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((r2_hidden @ (sk_C @ X0 @ (k2_struct_0 @ sk_B)) @ 
% 0.20/0.60           (k2_struct_0 @ sk_C_2))
% 0.20/0.60          | (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 0.20/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.60  thf('42', plain,
% 0.20/0.60      (![X6 : $i, X7 : $i]:
% 0.20/0.60         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.60  thf('43', plain,
% 0.20/0.60      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.60          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.60          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.60  thf('44', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.60         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.60          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.60  thf('45', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0)
% 0.20/0.60          | ~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60          | (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 0.20/0.60      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.60  thf('46', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60          | (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 0.20/0.60      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.60  thf('47', plain,
% 0.20/0.60      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_3)))
% 0.20/0.60         <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['22', '46'])).
% 0.20/0.60  thf('48', plain,
% 0.20/0.60      (![X12 : $i]:
% 0.20/0.60         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.60  thf('49', plain,
% 0.20/0.60      (![X26 : $i, X27 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X26)
% 0.20/0.60          | ~ (r1_xboole_0 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.20/0.60          | (r1_tsep_1 @ X27 @ X26)
% 0.20/0.60          | ~ (l1_struct_0 @ X27))),
% 0.20/0.60      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.60  thf('50', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.20/0.60          | ~ (l1_struct_0 @ X0)
% 0.20/0.60          | ~ (l1_struct_0 @ X0)
% 0.20/0.60          | (r1_tsep_1 @ X0 @ X1)
% 0.20/0.60          | ~ (l1_struct_0 @ X1))),
% 0.20/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.60  thf('51', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X1)
% 0.20/0.60          | (r1_tsep_1 @ X0 @ X1)
% 0.20/0.60          | ~ (l1_struct_0 @ X0)
% 0.20/0.60          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.20/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.60  thf('52', plain,
% 0.20/0.60      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.60         | (r1_tsep_1 @ sk_B @ sk_D_3)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['47', '51'])).
% 0.20/0.60  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.60  thf('54', plain,
% 0.20/0.60      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.60  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.60  thf('56', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('57', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('demod', [status(thm)], ['52', '55', '56'])).
% 0.20/0.60  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.60       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.60  thf('58', plain,
% 0.20/0.60      (![X28 : $i, X29 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X28)
% 0.20/0.60          | ~ (l1_struct_0 @ X29)
% 0.20/0.60          | (r1_tsep_1 @ X29 @ X28)
% 0.20/0.60          | ~ (r1_tsep_1 @ X28 @ X29))),
% 0.20/0.60      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.60  thf('59', plain,
% 0.20/0.60      ((((r1_tsep_1 @ sk_D_3 @ sk_B)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_D_3)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.60  thf('60', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.60  thf('62', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_D_3 @ sk_B)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.60  thf('63', plain,
% 0.20/0.60      ((~ (r1_tsep_1 @ sk_B @ sk_D_3) | ~ (r1_tsep_1 @ sk_D_3 @ sk_B))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('64', plain,
% 0.20/0.60      ((~ (r1_tsep_1 @ sk_D_3 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)))),
% 0.20/0.60      inference('split', [status(esa)], ['63'])).
% 0.20/0.60  thf('65', plain,
% 0.20/0.60      (~ ((r1_tsep_1 @ sk_D_3 @ sk_C_2)) | ((r1_tsep_1 @ sk_D_3 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['62', '64'])).
% 0.20/0.60  thf('66', plain,
% 0.20/0.60      (![X12 : $i]:
% 0.20/0.60         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.60  thf('67', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_C_2 @ sk_D_3)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('split', [status(esa)], ['1'])).
% 0.20/0.60  thf('68', plain,
% 0.20/0.60      (![X28 : $i, X29 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X28)
% 0.20/0.60          | ~ (l1_struct_0 @ X29)
% 0.20/0.60          | (r1_tsep_1 @ X29 @ X28)
% 0.20/0.60          | ~ (r1_tsep_1 @ X28 @ X29))),
% 0.20/0.60      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.60  thf('69', plain,
% 0.20/0.60      ((((r1_tsep_1 @ sk_D_3 @ sk_C_2)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_D_3)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.60  thf('70', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('71', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.60  thf('72', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_D_3 @ sk_C_2)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.60  thf('73', plain,
% 0.20/0.60      (![X26 : $i, X27 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X26)
% 0.20/0.60          | ~ (r1_tsep_1 @ X27 @ X26)
% 0.20/0.60          | (r1_xboole_0 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.20/0.60          | ~ (l1_struct_0 @ X27))),
% 0.20/0.60      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.60  thf('74', plain,
% 0.20/0.60      (((~ (l1_struct_0 @ sk_D_3)
% 0.20/0.60         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (u1_struct_0 @ sk_C_2))
% 0.20/0.60         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.60  thf('75', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('76', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.60  thf('77', plain,
% 0.20/0.60      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (u1_struct_0 @ sk_C_2)))
% 0.20/0.60         <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.20/0.60  thf('78', plain,
% 0.20/0.60      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['66', '77'])).
% 0.20/0.60  thf('79', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.60  thf('80', plain,
% 0.20/0.60      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_3) @ (k2_struct_0 @ sk_C_2)))
% 0.20/0.60         <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.60  thf('81', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_2))
% 0.20/0.60          | (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 0.20/0.60      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.60  thf('82', plain,
% 0.20/0.60      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_3)))
% 0.20/0.60         <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.60  thf('83', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X1)
% 0.20/0.60          | (r1_tsep_1 @ X0 @ X1)
% 0.20/0.60          | ~ (l1_struct_0 @ X0)
% 0.20/0.60          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.20/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.60  thf('84', plain,
% 0.20/0.60      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.60         | (r1_tsep_1 @ sk_B @ sk_D_3)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.60  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.60  thf('86', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('87', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.20/0.60  thf('88', plain,
% 0.20/0.60      ((~ (r1_tsep_1 @ sk_B @ sk_D_3)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_3)))),
% 0.20/0.60      inference('split', [status(esa)], ['63'])).
% 0.20/0.60  thf('89', plain,
% 0.20/0.60      (~ ((r1_tsep_1 @ sk_C_2 @ sk_D_3)) | ((r1_tsep_1 @ sk_B @ sk_D_3))),
% 0.20/0.60      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.60  thf('90', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.20/0.60      inference('demod', [status(thm)], ['52', '55', '56'])).
% 0.20/0.60  thf('91', plain,
% 0.20/0.60      ((~ (r1_tsep_1 @ sk_B @ sk_D_3)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_3)))),
% 0.20/0.60      inference('split', [status(esa)], ['63'])).
% 0.20/0.60  thf('92', plain,
% 0.20/0.60      (~ ((r1_tsep_1 @ sk_D_3 @ sk_C_2)) | ((r1_tsep_1 @ sk_B @ sk_D_3))),
% 0.20/0.60      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.60  thf('93', plain,
% 0.20/0.60      (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_3))),
% 0.20/0.60      inference('split', [status(esa)], ['63'])).
% 0.20/0.60  thf('94', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.20/0.60  thf('95', plain,
% 0.20/0.60      (![X28 : $i, X29 : $i]:
% 0.20/0.60         (~ (l1_struct_0 @ X28)
% 0.20/0.60          | ~ (l1_struct_0 @ X29)
% 0.20/0.60          | (r1_tsep_1 @ X29 @ X28)
% 0.20/0.60          | ~ (r1_tsep_1 @ X28 @ X29))),
% 0.20/0.60      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.60  thf('96', plain,
% 0.20/0.60      ((((r1_tsep_1 @ sk_D_3 @ sk_B)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_D_3)
% 0.20/0.60         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.60  thf('97', plain, ((l1_struct_0 @ sk_D_3)),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.60  thf('99', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_D_3 @ sk_B)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.20/0.60      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.60  thf('100', plain,
% 0.20/0.60      ((~ (r1_tsep_1 @ sk_D_3 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)))),
% 0.20/0.60      inference('split', [status(esa)], ['63'])).
% 0.20/0.60  thf('101', plain,
% 0.20/0.60      (~ ((r1_tsep_1 @ sk_C_2 @ sk_D_3)) | ((r1_tsep_1 @ sk_D_3 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.60  thf('102', plain,
% 0.20/0.60      (((r1_tsep_1 @ sk_C_2 @ sk_D_3)) | ((r1_tsep_1 @ sk_D_3 @ sk_C_2))),
% 0.20/0.60      inference('split', [status(esa)], ['1'])).
% 0.20/0.60  thf('103', plain, ($false),
% 0.20/0.60      inference('sat_resolution*', [status(thm)],
% 0.20/0.60                ['65', '89', '92', '93', '101', '102'])).
% 0.20/0.60  
% 0.20/0.60  % SZS output end Refutation
% 0.20/0.60  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
