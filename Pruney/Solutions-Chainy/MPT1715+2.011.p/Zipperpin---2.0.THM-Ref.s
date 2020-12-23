%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MYHJ52mInq

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 919 expanded)
%              Number of leaves         :   31 ( 282 expanded)
%              Depth                    :   18
%              Number of atoms          :  764 (12718 expanded)
%              Number of equality atoms :    6 (  26 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( r1_tsep_1 @ X20 @ X19 )
      | ~ ( r1_tsep_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( r1_tsep_1 @ X18 @ X17 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( r1_tarski @ ( k2_struct_0 @ X9 ) @ ( k2_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33','38'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ( r1_tsep_1 @ X18 @ X17 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('52',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( r1_tsep_1 @ X20 @ X19 )
      | ~ ( r1_tsep_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('54',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('57',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( r1_tsep_1 @ X18 @ X17 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('61',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('63',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('64',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['58','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('67',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('69',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('71',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('73',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('74',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( r1_tsep_1 @ X20 @ X19 )
      | ~ ( r1_tsep_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('76',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('83',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('87',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['81','84','85','86'])).

thf('88',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(simpl_trail,[status(thm)],['57','87'])).

thf('89',plain,
    ( $false
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['1','88'])).

thf('90',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['81','84','86','92','85'])).

thf('94',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['89','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MYHJ52mInq
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 73 iterations in 0.030s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(t24_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.49                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.49                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(d3_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X19)
% 0.21/0.49          | ~ (l1_struct_0 @ X20)
% 0.21/0.49          | (r1_tsep_1 @ X20 @ X19)
% 0.21/0.49          | ~ (r1_tsep_1 @ X19 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((((r1_tsep_1 @ sk_C_1 @ sk_D_2)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (l1_pre_topc @ X15)
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('13', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (l1_pre_topc @ X15)
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ((l1_pre_topc @ sk_D_2)),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('20', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.21/0.49  thf(d3_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_struct_0 @ B ) =>
% 0.21/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X17)
% 0.21/0.49          | ~ (r1_tsep_1 @ X18 @ X17)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.21/0.49          | ~ (l1_struct_0 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('25', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '26'])).
% 0.21/0.49  thf('28', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d9_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( ( ![C:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.49                     ( ?[D:$i]:
% 0.21/0.49                       ( ( m1_subset_1 @
% 0.21/0.49                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.49                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.49                         ( ( C ) =
% 0.21/0.49                           ( k9_subset_1 @
% 0.21/0.49                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.49               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_2, axiom,
% 0.21/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.49       ( ( ( C ) =
% 0.21/0.49           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.49         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_3, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.49               ( ![C:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.49                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X9)
% 0.21/0.49          | ~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.49          | (r1_tarski @ (k2_struct_0 @ X9) @ (k2_struct_0 @ X10))
% 0.21/0.49          | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (l1_pre_topc @ X15)
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['32', '33', '38'])).
% 0.21/0.49  thf(t63_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.21/0.49          | (r1_xboole_0 @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0)
% 0.21/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ sk_C_1) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X17)
% 0.21/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.21/0.49          | (r1_tsep_1 @ X18 @ X17)
% 0.21/0.49          | ~ (l1_struct_0 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.21/0.49          | ~ (l1_struct_0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X1)
% 0.21/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.49         | (r1_tsep_1 @ sk_B @ sk_D_2)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '46'])).
% 0.21/0.49  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X19)
% 0.21/0.49          | ~ (l1_struct_0 @ X20)
% 0.21/0.49          | (r1_tsep_1 @ X20 @ X19)
% 0.21/0.49          | ~ (r1_tsep_1 @ X19 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((((r1_tsep_1 @ sk_D_2 @ sk_B)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X17)
% 0.21/0.49          | ~ (r1_tsep_1 @ X18 @ X17)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.21/0.49          | ~ (l1_struct_0 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('63', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['58', '64'])).
% 0.21/0.49  thf('66', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ X0)
% 0.21/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ sk_C_1) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X1)
% 0.21/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.49         | (r1_tsep_1 @ sk_B @ sk_D_2)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.49  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('73', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X19)
% 0.21/0.49          | ~ (l1_struct_0 @ X20)
% 0.21/0.49          | (r1_tsep_1 @ X20 @ X19)
% 0.21/0.49          | ~ (r1_tsep_1 @ X19 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      ((((r1_tsep_1 @ sk_D_2 @ sk_B)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.49  thf('82', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.49  thf('85', plain,
% 0.21/0.49      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('87', plain, (((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['81', '84', '85', '86'])).
% 0.21/0.49  thf('88', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['57', '87'])).
% 0.21/0.49  thf('89', plain, (($false) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '88'])).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('92', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.49  thf('93', plain, (~ ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)],
% 0.21/0.49                ['81', '84', '86', '92', '85'])).
% 0.21/0.49  thf('94', plain, ($false),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['89', '93'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
