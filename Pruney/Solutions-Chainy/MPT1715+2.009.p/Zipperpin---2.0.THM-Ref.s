%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w1xHZsawd7

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:24 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  141 (1005 expanded)
%              Number of leaves         :   35 ( 308 expanded)
%              Depth                    :   18
%              Number of atoms          :  888 (13678 expanded)
%              Number of equality atoms :   11 (  56 expanded)
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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t24_tmap_1,conjecture,(
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
                   => ( ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) )
                      | ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) )).

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
                     => ( ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) )
                        | ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_3 )
    | ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
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

thf('3',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
    | ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X29 )
      | ( r1_tsep_1 @ X29 @ X28 )
      | ~ ( r1_tsep_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_D_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_D_3 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( r1_tsep_1 @ X27 @ X26 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['32','33','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) )
    = ( k2_struct_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('59',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('62',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X29 )
      | ( r1_tsep_1 @ X29 @ X28 )
      | ~ ( r1_tsep_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('64',plain,
    ( ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('67',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(split,[status(esa)],['3'])).

thf('70',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( r1_tsep_1 @ X27 @ X26 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('71',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('73',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('74',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('79',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('81',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_D_3 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('83',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('84',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( l1_struct_0 @ X29 )
      | ( r1_tsep_1 @ X29 @ X28 )
      | ~ ( r1_tsep_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('86',plain,
    ( ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_3 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_D_3 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('89',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_C_2 @ sk_D_3 )
    | ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
    | ~ ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_D_3 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_D_3 @ sk_C_2 )
    | ( r1_tsep_1 @ sk_C_2 @ sk_D_3 ) ),
    inference(split,[status(esa)],['3'])).

thf('97',plain,(
    r1_tsep_1 @ sk_D_3 @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['91','94','95','96'])).

thf('98',plain,(
    r1_tsep_1 @ sk_D_3 @ sk_B ),
    inference(simpl_trail,[status(thm)],['67','97'])).

thf('99',plain,
    ( $false
   <= ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference(demod,[status(thm)],['1','98'])).

thf('100',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('101',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_3 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_3 )
    | ~ ( r1_tsep_1 @ sk_D_3 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( r1_tsep_1 @ sk_D_3 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['91','94','96','102','95'])).

thf('104',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['99','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w1xHZsawd7
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 328 iterations in 0.190s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.47/0.65  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.47/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.47/0.65  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.47/0.65  thf(t24_tmap_1, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65               ( ![D:$i]:
% 0.47/0.65                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                   ( ( m1_pre_topc @ B @ C ) =>
% 0.47/0.65                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.47/0.65                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.47/0.65                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.65            ( l1_pre_topc @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.47/0.65              ( ![C:$i]:
% 0.47/0.65                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.47/0.65                  ( ![D:$i]:
% 0.47/0.65                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.47/0.65                      ( ( m1_pre_topc @ B @ C ) =>
% 0.47/0.65                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.47/0.65                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.47/0.65                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      ((~ (r1_tsep_1 @ sk_B @ sk_D_3) | ~ (r1_tsep_1 @ sk_D_3 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      ((~ (r1_tsep_1 @ sk_D_3 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf(d3_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X12 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_C_2 @ sk_D_3) | (r1_tsep_1 @ sk_D_3 @ sk_C_2))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_D_3 @ sk_C_2)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf(symmetry_r1_tsep_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.65       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X28 : $i, X29 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X28)
% 0.47/0.65          | ~ (l1_struct_0 @ X29)
% 0.47/0.65          | (r1_tsep_1 @ X29 @ X28)
% 0.47/0.65          | ~ (r1_tsep_1 @ X28 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      ((((r1_tsep_1 @ sk_C_2 @ sk_D_3)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_C_2)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.65  thf('7', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(dt_m1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (![X24 : $i, X25 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X24 @ X25)
% 0.47/0.65          | (l1_pre_topc @ X24)
% 0.47/0.65          | ~ (l1_pre_topc @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.47/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('11', plain, ((l1_pre_topc @ sk_C_2)),
% 0.47/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.65  thf(dt_l1_pre_topc, axiom,
% 0.47/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.65  thf('13', plain, ((l1_struct_0 @ sk_C_2)),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('14', plain, ((m1_pre_topc @ sk_D_3 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X24 : $i, X25 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X24 @ X25)
% 0.47/0.65          | (l1_pre_topc @ X24)
% 0.47/0.65          | ~ (l1_pre_topc @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_3))),
% 0.47/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.65  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('18', plain, ((l1_pre_topc @ sk_D_3)),
% 0.47/0.65      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.65  thf('20', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_C_2 @ sk_D_3)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.47/0.65  thf(d3_tsep_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( l1_struct_0 @ B ) =>
% 0.47/0.65           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.47/0.65             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X26 : $i, X27 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X26)
% 0.47/0.65          | ~ (r1_tsep_1 @ X27 @ X26)
% 0.47/0.65          | (r1_xboole_0 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.47/0.65          | ~ (l1_struct_0 @ X27))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (((~ (l1_struct_0 @ sk_C_2)
% 0.47/0.65         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.65  thf('24', plain, ((l1_struct_0 @ sk_C_2)),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('25', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3)))
% 0.47/0.65         <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      ((((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['2', '26'])).
% 0.47/0.65  thf('28', plain, ((l1_struct_0 @ sk_C_2)),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3)))
% 0.47/0.65         <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('demod', [status(thm)], ['27', '28'])).
% 0.47/0.65  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_C_2)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d9_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( l1_pre_topc @ B ) =>
% 0.47/0.65           ( ( m1_pre_topc @ B @ A ) <=>
% 0.47/0.65             ( ( ![C:$i]:
% 0.47/0.65                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.65                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.47/0.65                     ( ?[D:$i]:
% 0.47/0.65                       ( ( m1_subset_1 @
% 0.47/0.65                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.47/0.65                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.47/0.65                         ( ( C ) =
% 0.47/0.65                           ( k9_subset_1 @
% 0.47/0.65                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.47/0.65               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.47/0.65  thf(zf_stmt_2, axiom,
% 0.47/0.65    (![D:$i,C:$i,B:$i,A:$i]:
% 0.47/0.65     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.47/0.65       ( ( ( C ) =
% 0.47/0.65           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.47/0.65         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.47/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_3, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( l1_pre_topc @ B ) =>
% 0.47/0.65           ( ( m1_pre_topc @ B @ A ) <=>
% 0.47/0.65             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.47/0.65               ( ![C:$i]:
% 0.47/0.65                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.65                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.47/0.65                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X18 : $i, X19 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X18)
% 0.47/0.65          | ~ (m1_pre_topc @ X18 @ X19)
% 0.47/0.65          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 0.47/0.65          | ~ (l1_pre_topc @ X19))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      ((~ (l1_pre_topc @ sk_C_2)
% 0.47/0.65        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))
% 0.47/0.65        | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain, ((l1_pre_topc @ sk_C_2)),
% 0.47/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.65  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X24 : $i, X25 : $i]:
% 0.47/0.65         (~ (m1_pre_topc @ X24 @ X25)
% 0.47/0.65          | (l1_pre_topc @ X24)
% 0.47/0.65          | ~ (l1_pre_topc @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.47/0.65  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.65  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))),
% 0.47/0.65      inference('demod', [status(thm)], ['32', '33', '38'])).
% 0.47/0.65  thf(t12_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X10 : $i, X11 : $i]:
% 0.47/0.65         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (((k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))
% 0.47/0.65         = (k2_struct_0 @ sk_C_2))),
% 0.47/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.65  thf(t3_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.47/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.65  thf(d3_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.47/0.65       ( ![D:$i]:
% 0.47/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.65           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X0 @ X3)
% 0.47/0.65          | (r2_hidden @ X0 @ X2)
% 0.47/0.65          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.47/0.65         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.47/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X0 @ X1)
% 0.47/0.65          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['43', '45'])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.47/0.65          | ~ (r2_hidden @ X8 @ X9)
% 0.47/0.65          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X1 @ X2)
% 0.47/0.65          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3)
% 0.47/0.65          | ~ (r2_hidden @ (sk_C @ X2 @ X1) @ X3))),
% 0.47/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X1 @ X0)
% 0.47/0.65          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0)
% 0.47/0.65          | (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['42', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0)
% 0.47/0.65          | (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ X0)
% 0.47/0.65          | (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['41', '50'])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_3)))
% 0.47/0.65         <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['29', '51'])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      (![X12 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      (![X26 : $i, X27 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X26)
% 0.47/0.65          | ~ (r1_xboole_0 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.47/0.65          | (r1_tsep_1 @ X27 @ X26)
% 0.47/0.65          | ~ (l1_struct_0 @ X27))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | (r1_tsep_1 @ X0 @ X1)
% 0.47/0.65          | ~ (l1_struct_0 @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X1)
% 0.47/0.65          | (r1_tsep_1 @ X0 @ X1)
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (((~ (l1_struct_0 @ sk_B)
% 0.47/0.65         | (r1_tsep_1 @ sk_B @ sk_D_3)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['52', '56'])).
% 0.47/0.65  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.65  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('61', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      (![X28 : $i, X29 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X28)
% 0.47/0.65          | ~ (l1_struct_0 @ X29)
% 0.47/0.65          | (r1_tsep_1 @ X29 @ X28)
% 0.47/0.65          | ~ (r1_tsep_1 @ X28 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      ((((r1_tsep_1 @ sk_D_3 @ sk_B)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.65  thf('65', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_D_3 @ sk_B)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      (![X12 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_C_2 @ sk_D_3)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (![X26 : $i, X27 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X26)
% 0.47/0.65          | ~ (r1_tsep_1 @ X27 @ X26)
% 0.47/0.65          | (r1_xboole_0 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.47/0.65          | ~ (l1_struct_0 @ X27))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      (((~ (l1_struct_0 @ sk_C_2)
% 0.47/0.65         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['69', '70'])).
% 0.47/0.65  thf('72', plain, ((l1_struct_0 @ sk_C_2)),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('73', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('74', plain,
% 0.47/0.65      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3)))
% 0.47/0.65         <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      ((((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['68', '74'])).
% 0.47/0.65  thf('76', plain, ((l1_struct_0 @ sk_C_2)),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      (((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_D_3)))
% 0.47/0.65         <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('demod', [status(thm)], ['75', '76'])).
% 0.47/0.65  thf('78', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ X0)
% 0.47/0.65          | (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['41', '50'])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_3)))
% 0.47/0.65         <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.47/0.65  thf('80', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X1)
% 0.47/0.65          | (r1_tsep_1 @ X0 @ X1)
% 0.47/0.65          | ~ (l1_struct_0 @ X0)
% 0.47/0.65          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      (((~ (l1_struct_0 @ sk_B)
% 0.47/0.65         | (r1_tsep_1 @ sk_B @ sk_D_3)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['79', '80'])).
% 0.47/0.65  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('83', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('84', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.47/0.65  thf('85', plain,
% 0.47/0.65      (![X28 : $i, X29 : $i]:
% 0.47/0.65         (~ (l1_struct_0 @ X28)
% 0.47/0.65          | ~ (l1_struct_0 @ X29)
% 0.47/0.65          | (r1_tsep_1 @ X29 @ X28)
% 0.47/0.65          | ~ (r1_tsep_1 @ X28 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      ((((r1_tsep_1 @ sk_D_3 @ sk_B)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_D_3)
% 0.47/0.65         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.65  thf('87', plain, ((l1_struct_0 @ sk_D_3)),
% 0.47/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.65  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_D_3 @ sk_B)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.47/0.65  thf('90', plain,
% 0.47/0.65      ((~ (r1_tsep_1 @ sk_D_3 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      (~ ((r1_tsep_1 @ sk_C_2 @ sk_D_3)) | ((r1_tsep_1 @ sk_D_3 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.65  thf('92', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D_3)))),
% 0.47/0.65      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.47/0.65  thf('93', plain,
% 0.47/0.65      ((~ (r1_tsep_1 @ sk_B @ sk_D_3)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_3)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('94', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_B @ sk_D_3)) | ~ ((r1_tsep_1 @ sk_C_2 @ sk_D_3))),
% 0.47/0.65      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.65  thf('95', plain,
% 0.47/0.65      (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_3))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('96', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_D_3 @ sk_C_2)) | ((r1_tsep_1 @ sk_C_2 @ sk_D_3))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf('97', plain, (((r1_tsep_1 @ sk_D_3 @ sk_C_2))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['91', '94', '95', '96'])).
% 0.47/0.65  thf('98', plain, ((r1_tsep_1 @ sk_D_3 @ sk_B)),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['67', '97'])).
% 0.47/0.65  thf('99', plain, (($false) <= (~ ((r1_tsep_1 @ sk_D_3 @ sk_B)))),
% 0.47/0.65      inference('demod', [status(thm)], ['1', '98'])).
% 0.47/0.65  thf('100', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_B @ sk_D_3)) <= (((r1_tsep_1 @ sk_D_3 @ sk_C_2)))),
% 0.47/0.65      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.47/0.65  thf('101', plain,
% 0.47/0.65      ((~ (r1_tsep_1 @ sk_B @ sk_D_3)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_3)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('102', plain,
% 0.47/0.65      (((r1_tsep_1 @ sk_B @ sk_D_3)) | ~ ((r1_tsep_1 @ sk_D_3 @ sk_C_2))),
% 0.47/0.65      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.65  thf('103', plain, (~ ((r1_tsep_1 @ sk_D_3 @ sk_B))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)],
% 0.47/0.65                ['91', '94', '96', '102', '95'])).
% 0.47/0.65  thf('104', plain, ($false),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['99', '103'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
