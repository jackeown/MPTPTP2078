%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hAeipSeVcS

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 556 expanded)
%              Number of leaves         :   35 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  814 (6846 expanded)
%              Number of equality atoms :   40 ( 302 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t33_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v3_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tops_2])).

thf('0',plain,(
    ~ ( v3_pre_topc @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_3 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_3 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

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

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ X32 @ ( k2_struct_0 @ X29 ) )
       != X31 )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('14',plain,(
    ! [X29: $i,X30: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ X32 @ ( k2_struct_0 @ X29 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X29 ) @ X32 @ ( k2_struct_0 @ X29 ) ) @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('23',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( l1_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['23','28'])).

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

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( k2_struct_0 @ X20 ) @ ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['23','28'])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( l1_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('38',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) )
    = ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X14
       != ( k1_pre_topc @ X13 @ X12 ) )
      | ( ( k2_struct_0 @ X14 )
        = X12 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( v1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X13 @ X12 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X13 @ X12 ) @ X13 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['23','28'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('50',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('51',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('53',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('55',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['47','48','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('57',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['47','48','53','54'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','55','56','57'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20','58','59','60','61','62'])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['2','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hAeipSeVcS
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:44:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 77 iterations in 0.044s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(t33_tops_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51               ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.51                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_pre_topc @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51                  ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.51                    ( ![D:$i]:
% 0.21/0.51                      ( ( m1_subset_1 @
% 0.21/0.51                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.51                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 0.21/0.51  thf('0', plain, (~ (v3_pre_topc @ sk_D_3 @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, (((sk_D_3) = (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain, (((sk_D_3) = (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(commutativity_k9_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.21/0.51           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.21/0.51           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X0 @ sk_B)
% 0.21/0.51           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.51  thf(t32_tops_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51               ( ( v3_pre_topc @ C @ B ) <=>
% 0.21/0.51                 ( ?[D:$i]:
% 0.21/0.51                   ( ( ( k9_subset_1 @
% 0.21/0.51                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.21/0.51                       ( C ) ) & 
% 0.21/0.51                     ( v3_pre_topc @ D @ A ) & 
% 0.21/0.51                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X29 @ X30)
% 0.21/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X29) @ X32 @ (k2_struct_0 @ X29))
% 0.21/0.51              != (X31))
% 0.21/0.51          | ~ (v3_pre_topc @ X32 @ X30)
% 0.21/0.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.51          | (v3_pre_topc @ X31 @ X29)
% 0.21/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.51          | ~ (l1_pre_topc @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [t32_tops_2])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i, X32 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X30)
% 0.21/0.51          | ~ (m1_subset_1 @ 
% 0.21/0.51               (k9_subset_1 @ (u1_struct_0 @ X29) @ X32 @ (k2_struct_0 @ X29)) @ 
% 0.21/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.51          | (v3_pre_topc @ 
% 0.21/0.51             (k9_subset_1 @ (u1_struct_0 @ X29) @ X32 @ (k2_struct_0 @ X29)) @ 
% 0.21/0.51             X29)
% 0.21/0.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.51          | ~ (v3_pre_topc @ X32 @ X30)
% 0.21/0.51          | ~ (m1_pre_topc @ X29 @ X30))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.51          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v3_pre_topc @ 
% 0.21/0.51             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 0.21/0.51              (k2_struct_0 @ sk_C_1)) @ 
% 0.21/0.51             sk_C_1)
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.51  thf(commutativity_k2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf(t12_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(dt_k1_pre_topc, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.21/0.51         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X25)
% 0.21/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.51          | (m1_pre_topc @ (k1_pre_topc @ X25 @ X26) @ X25))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.51          | (l1_pre_topc @ X27)
% 0.21/0.51          | ~ (l1_pre_topc @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('26', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '28'])).
% 0.21/0.51  thf(d9_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_pre_topc @ B ) =>
% 0.21/0.51           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.51             ( ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.51                     ( ?[D:$i]:
% 0.21/0.51                       ( ( m1_subset_1 @
% 0.21/0.51                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.51                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.51                         ( ( C ) =
% 0.21/0.51                           ( k9_subset_1 @
% 0.21/0.51                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.51               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_2, axiom,
% 0.21/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.51       ( ( ( C ) =
% 0.21/0.51           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.51         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_pre_topc @ B ) =>
% 0.21/0.51           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.51             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.51               ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.51                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.51                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X20)
% 0.21/0.51          | ~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.51          | (r1_tarski @ (k2_struct_0 @ X20) @ (k2_struct_0 @ X21))
% 0.21/0.51          | ~ (l1_pre_topc @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.21/0.51           (k2_struct_0 @ sk_C_1))
% 0.21/0.51        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.21/0.51         (k2_struct_0 @ sk_C_1))
% 0.21/0.51        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '28'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.51          | (l1_pre_topc @ X27)
% 0.21/0.51          | ~ (l1_pre_topc @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('38', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.21/0.51        (k2_struct_0 @ sk_C_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '38'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((k3_xboole_0 @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.21/0.51         (k2_struct_0 @ sk_C_1))
% 0.21/0.51         = (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ 
% 0.21/0.51         (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)))
% 0.21/0.51         = (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(d10_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.21/0.51                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.51          | ((X14) != (k1_pre_topc @ X13 @ X12))
% 0.21/0.51          | ((k2_struct_0 @ X14) = (X12))
% 0.21/0.51          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.51          | ~ (v1_pre_topc @ X14)
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X13)
% 0.21/0.51          | ~ (v1_pre_topc @ (k1_pre_topc @ X13 @ X12))
% 0.21/0.51          | ~ (m1_pre_topc @ (k1_pre_topc @ X13 @ X12) @ X13)
% 0.21/0.51          | ((k2_struct_0 @ (k1_pre_topc @ X13 @ X12)) = (X12))
% 0.21/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 0.21/0.51        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.21/0.51        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.51  thf('48', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['23', '28'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X25)
% 0.21/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.51          | (v1_pre_topc @ (k1_pre_topc @ X25 @ X26)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('53', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('55', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48', '53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('57', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48', '53', '54'])).
% 0.21/0.51  thf('58', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '55', '56', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X0 @ sk_B)
% 0.21/0.51           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('62', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '55', '56', '57'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.51          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v3_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['15', '20', '58', '59', '60', '61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v3_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.51        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.21/0.51        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '63'])).
% 0.21/0.51  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain, ((v3_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.21/0.51  thf('69', plain, ($false), inference('demod', [status(thm)], ['2', '68'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
