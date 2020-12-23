%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IuLZDIUtmJ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:48 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 700 expanded)
%              Number of leaves         :   23 ( 198 expanded)
%              Depth                    :   21
%              Number of atoms          : 2499 (12942 expanded)
%              Number of equality atoms :   70 ( 348 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_tops_1 @ X15 @ X14 ) @ ( k1_tops_1 @ X15 @ X16 ) )
        = ( k1_tops_1 @ X15 @ ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','56','57','58','59','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_tops_1 @ X15 @ X14 ) @ ( k1_tops_1 @ X15 @ X16 ) )
        = ( k1_tops_1 @ X15 @ ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','72'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) )
      = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','114','115','116','117','118'])).

thf('120',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('135',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('137',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_tops_1 @ X15 @ X14 ) @ ( k1_tops_1 @ X15 @ X16 ) )
        = ( k1_tops_1 @ X15 @ ( k9_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('147',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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

thf('160',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('161',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','173'])).

thf('175',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['147','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('177',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('188',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('189',plain,
    ( ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('192',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','92','135','136','190','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IuLZDIUtmJ
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.41/2.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.41/2.64  % Solved by: fo/fo7.sh
% 2.41/2.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.41/2.64  % done 2622 iterations in 2.177s
% 2.41/2.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.41/2.64  % SZS output start Refutation
% 2.41/2.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.41/2.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.41/2.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.41/2.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.41/2.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.41/2.64  thf(sk_B_type, type, sk_B: $i).
% 2.41/2.64  thf(sk_C_type, type, sk_C: $i).
% 2.41/2.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.41/2.64  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.41/2.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.41/2.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.41/2.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.41/2.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.41/2.64  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 2.41/2.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.41/2.64  thf(sk_A_type, type, sk_A: $i).
% 2.41/2.64  thf(t4_connsp_2, conjecture,
% 2.41/2.64    (![A:$i]:
% 2.41/2.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.41/2.64       ( ![B:$i]:
% 2.41/2.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.41/2.64           ( ![C:$i]:
% 2.41/2.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64               ( ![D:$i]:
% 2.41/2.64                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 2.41/2.64                       ( m1_connsp_2 @ D @ A @ B ) ) <=>
% 2.41/2.64                     ( m1_connsp_2 @
% 2.41/2.64                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 2.41/2.64  thf(zf_stmt_0, negated_conjecture,
% 2.41/2.64    (~( ![A:$i]:
% 2.41/2.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.41/2.64            ( l1_pre_topc @ A ) ) =>
% 2.41/2.64          ( ![B:$i]:
% 2.41/2.64            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.41/2.64              ( ![C:$i]:
% 2.41/2.64                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64                  ( ![D:$i]:
% 2.41/2.64                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 2.41/2.64                          ( m1_connsp_2 @ D @ A @ B ) ) <=>
% 2.41/2.64                        ( m1_connsp_2 @
% 2.41/2.64                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 2.41/2.64    inference('cnf.neg', [status(esa)], [t4_connsp_2])).
% 2.41/2.64  thf('0', plain,
% 2.41/2.64      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B)
% 2.41/2.64        | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('1', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)) | 
% 2.41/2.64       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B))),
% 2.41/2.64      inference('split', [status(esa)], ['0'])).
% 2.41/2.64  thf('2', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf(redefinition_k9_subset_1, axiom,
% 2.41/2.64    (![A:$i,B:$i,C:$i]:
% 2.41/2.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.64       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.41/2.64  thf('3', plain,
% 2.41/2.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.41/2.64         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 2.41/2.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.41/2.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.41/2.64  thf('4', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['2', '3'])).
% 2.41/2.64  thf('5', plain,
% 2.41/2.64      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B)
% 2.41/2.64        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('6', plain,
% 2.41/2.64      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('split', [status(esa)], ['5'])).
% 2.41/2.64  thf('7', plain,
% 2.41/2.64      (((m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup+', [status(thm)], ['4', '6'])).
% 2.41/2.64  thf('8', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf(dt_k9_subset_1, axiom,
% 2.41/2.64    (![A:$i,B:$i,C:$i]:
% 2.41/2.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.41/2.64       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.41/2.64  thf('9', plain,
% 2.41/2.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.41/2.64         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 2.41/2.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 2.41/2.64      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 2.41/2.64  thf('10', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1) @ 
% 2.41/2.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['8', '9'])).
% 2.41/2.64  thf('11', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['2', '3'])).
% 2.41/2.64  thf('12', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_D_1) @ 
% 2.41/2.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['10', '11'])).
% 2.41/2.64  thf(d1_connsp_2, axiom,
% 2.41/2.64    (![A:$i]:
% 2.41/2.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.41/2.64       ( ![B:$i]:
% 2.41/2.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.41/2.64           ( ![C:$i]:
% 2.41/2.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 2.41/2.64                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.41/2.64  thf('13', plain,
% 2.41/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.41/2.64          | ~ (m1_connsp_2 @ X19 @ X18 @ X17)
% 2.41/2.64          | (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 2.41/2.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.41/2.64          | ~ (l1_pre_topc @ X18)
% 2.41/2.64          | ~ (v2_pre_topc @ X18)
% 2.41/2.64          | (v2_struct_0 @ X18))),
% 2.41/2.64      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.41/2.64  thf('14', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | ~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 2.41/2.64          | ~ (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_D_1) @ sk_A @ X1)
% 2.41/2.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['12', '13'])).
% 2.41/2.64  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('17', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 2.41/2.64          | ~ (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_D_1) @ sk_A @ X1)
% 2.41/2.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['14', '15', '16'])).
% 2.41/2.64  thf('18', plain,
% 2.41/2.64      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.41/2.64         | (r2_hidden @ sk_B @ 
% 2.41/2.64            (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))
% 2.41/2.64         | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['7', '17'])).
% 2.41/2.64  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('20', plain,
% 2.41/2.64      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))
% 2.41/2.64         | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('demod', [status(thm)], ['18', '19'])).
% 2.41/2.64  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('22', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1))))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['20', '21'])).
% 2.41/2.64  thf(d4_xboole_0, axiom,
% 2.41/2.64    (![A:$i,B:$i,C:$i]:
% 2.41/2.64     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.41/2.64       ( ![D:$i]:
% 2.41/2.64         ( ( r2_hidden @ D @ C ) <=>
% 2.41/2.64           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.41/2.64  thf('23', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.41/2.64         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.41/2.64          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('24', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.41/2.64         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.41/2.64          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('25', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.41/2.64         (~ (r2_hidden @ X0 @ X1)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ X2)
% 2.41/2.64          | (r2_hidden @ X0 @ X3)
% 2.41/2.64          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('26', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.64         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | ~ (r2_hidden @ X0 @ X2)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ X1))),
% 2.41/2.64      inference('simplify', [status(thm)], ['25'])).
% 2.41/2.64  thf('27', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 2.41/2.64          | ((X2) = (k3_xboole_0 @ X0 @ X1))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3)
% 2.41/2.64          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X0)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['24', '26'])).
% 2.41/2.64  thf('28', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 2.41/2.64          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 2.41/2.64          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2))),
% 2.41/2.64      inference('sup-', [status(thm)], ['23', '27'])).
% 2.41/2.64  thf('29', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 2.41/2.64          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2))),
% 2.41/2.64      inference('simplify', [status(thm)], ['28'])).
% 2.41/2.64  thf('30', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ X0) @ 
% 2.41/2.64           (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.64      inference('eq_fact', [status(thm)], ['29'])).
% 2.41/2.64  thf('31', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.41/2.64         (~ (r2_hidden @ X4 @ X3)
% 2.41/2.64          | (r2_hidden @ X4 @ X1)
% 2.41/2.64          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('32', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.41/2.64         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['31'])).
% 2.41/2.64  thf('33', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))
% 2.41/2.64          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ X0) @ X1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['30', '32'])).
% 2.41/2.64  thf('34', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.41/2.64         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('35', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X1) @ 
% 2.41/2.64               (k3_xboole_0 @ X0 @ X1))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X1) @ X1)
% 2.41/2.64          | ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['33', '34'])).
% 2.41/2.64  thf('36', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X1) @ X1)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X1) @ 
% 2.41/2.64               (k3_xboole_0 @ X0 @ X1))
% 2.41/2.64          | ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['35'])).
% 2.41/2.64  thf('37', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.41/2.64         (~ (r2_hidden @ X4 @ X3)
% 2.41/2.64          | (r2_hidden @ X4 @ X2)
% 2.41/2.64          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('38', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.41/2.64         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['37'])).
% 2.41/2.64  thf('39', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X1) @ 
% 2.41/2.64               (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.64      inference('clc', [status(thm)], ['36', '38'])).
% 2.41/2.64  thf('40', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ X0) @ 
% 2.41/2.64           (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.64      inference('eq_fact', [status(thm)], ['29'])).
% 2.41/2.64  thf('41', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 2.41/2.64      inference('clc', [status(thm)], ['39', '40'])).
% 2.41/2.64  thf('42', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('43', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_D_1) @ 
% 2.41/2.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['10', '11'])).
% 2.41/2.64  thf(t46_tops_1, axiom,
% 2.41/2.64    (![A:$i]:
% 2.41/2.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.41/2.64       ( ![B:$i]:
% 2.41/2.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64           ( ![C:$i]:
% 2.41/2.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.41/2.64               ( ( k9_subset_1 @
% 2.41/2.64                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 2.41/2.64                   ( k1_tops_1 @ A @ C ) ) =
% 2.41/2.64                 ( k1_tops_1 @
% 2.41/2.64                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 2.41/2.64  thf('44', plain,
% 2.41/2.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ (k1_tops_1 @ X15 @ X14) @ 
% 2.41/2.64              (k1_tops_1 @ X15 @ X16))
% 2.41/2.64              = (k1_tops_1 @ X15 @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ X15) @ X14 @ X16)))
% 2.41/2.64          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.64          | ~ (l1_pre_topc @ X15)
% 2.41/2.64          | ~ (v2_pre_topc @ X15))),
% 2.41/2.64      inference('cnf', [status(esa)], [t46_tops_1])).
% 2.41/2.64  thf('45', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ X1))
% 2.41/2.64              = (k1_tops_1 @ sk_A @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64                  (k3_xboole_0 @ X0 @ sk_D_1) @ X1))))),
% 2.41/2.64      inference('sup-', [status(thm)], ['43', '44'])).
% 2.41/2.64  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('48', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ X1))
% 2.41/2.64              = (k1_tops_1 @ sk_A @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64                  (k3_xboole_0 @ X0 @ sk_D_1) @ X1))))),
% 2.41/2.64      inference('demod', [status(thm)], ['45', '46', '47'])).
% 2.41/2.64  thf('49', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)) @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64           = (k1_tops_1 @ sk_A @ 
% 2.41/2.64              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64               (k3_xboole_0 @ X0 @ sk_D_1) @ sk_D_1)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['42', '48'])).
% 2.41/2.64  thf('50', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf(dt_k1_tops_1, axiom,
% 2.41/2.64    (![A:$i,B:$i]:
% 2.41/2.64     ( ( ( l1_pre_topc @ A ) & 
% 2.41/2.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.41/2.64       ( m1_subset_1 @
% 2.41/2.64         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.41/2.64  thf('51', plain,
% 2.41/2.64      (![X12 : $i, X13 : $i]:
% 2.41/2.64         (~ (l1_pre_topc @ X12)
% 2.41/2.64          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 2.41/2.64          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 2.41/2.64             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 2.41/2.64      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.41/2.64  thf('52', plain,
% 2.41/2.64      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 2.41/2.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64        | ~ (l1_pre_topc @ sk_A))),
% 2.41/2.64      inference('sup-', [status(thm)], ['50', '51'])).
% 2.41/2.64  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('54', plain,
% 2.41/2.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 2.41/2.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['52', '53'])).
% 2.41/2.64  thf('55', plain,
% 2.41/2.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.41/2.64         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 2.41/2.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.41/2.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.41/2.64  thf('56', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64           = (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['54', '55'])).
% 2.41/2.64  thf('57', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 2.41/2.64      inference('clc', [status(thm)], ['39', '40'])).
% 2.41/2.64  thf('58', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['2', '3'])).
% 2.41/2.64  thf('59', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 2.41/2.64      inference('clc', [status(thm)], ['39', '40'])).
% 2.41/2.64  thf('60', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 2.41/2.64      inference('clc', [status(thm)], ['39', '40'])).
% 2.41/2.64  thf('61', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.41/2.64         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.41/2.64          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('62', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.41/2.64          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('eq_fact', [status(thm)], ['61'])).
% 2.41/2.64  thf('63', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.41/2.64         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['31'])).
% 2.41/2.64  thf('64', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.64         (((k3_xboole_0 @ X1 @ X0)
% 2.41/2.64            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 2.41/2.64          | (r2_hidden @ 
% 2.41/2.64             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 2.41/2.64             X1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['62', '63'])).
% 2.41/2.64  thf('65', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.41/2.64          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('eq_fact', [status(thm)], ['61'])).
% 2.41/2.64  thf('66', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.41/2.64         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.41/2.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.64  thf('67', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.41/2.64          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['65', '66'])).
% 2.41/2.64  thf('68', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.41/2.64          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['67'])).
% 2.41/2.64  thf('69', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.41/2.64          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('eq_fact', [status(thm)], ['61'])).
% 2.41/2.64  thf('70', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.41/2.64          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.41/2.64      inference('clc', [status(thm)], ['68', '69'])).
% 2.41/2.64  thf('71', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (((k3_xboole_0 @ X0 @ X1)
% 2.41/2.64            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 2.41/2.64          | ((k3_xboole_0 @ X0 @ X1)
% 2.41/2.64              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 2.41/2.64      inference('sup-', [status(thm)], ['64', '70'])).
% 2.41/2.64  thf('72', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((k3_xboole_0 @ X0 @ X1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['71'])).
% 2.41/2.64  thf('73', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((k3_xboole_0 @ X0 @ X1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('sup+', [status(thm)], ['60', '72'])).
% 2.41/2.64  thf('74', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 2.41/2.64           = (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ X0)))),
% 2.41/2.64      inference('demod', [status(thm)], ['49', '56', '57', '58', '59', '73'])).
% 2.41/2.64  thf('75', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.41/2.64         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['31'])).
% 2.41/2.64  thf('76', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ X0)))
% 2.41/2.64          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['74', '75'])).
% 2.41/2.64  thf('77', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 2.41/2.64          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['41', '76'])).
% 2.41/2.64  thf('78', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['22', '77'])).
% 2.41/2.64  thf('79', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('80', plain,
% 2.41/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.41/2.64          | ~ (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 2.41/2.64          | (m1_connsp_2 @ X19 @ X18 @ X17)
% 2.41/2.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.41/2.64          | ~ (l1_pre_topc @ X18)
% 2.41/2.64          | ~ (v2_pre_topc @ X18)
% 2.41/2.64          | (v2_struct_0 @ X18))),
% 2.41/2.64      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.41/2.64  thf('81', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | ~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['79', '80'])).
% 2.41/2.64  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('84', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['81', '82', '83'])).
% 2.41/2.64  thf('85', plain,
% 2.41/2.64      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.41/2.64         | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)
% 2.41/2.64         | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['78', '84'])).
% 2.41/2.64  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('87', plain,
% 2.41/2.64      ((((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('demod', [status(thm)], ['85', '86'])).
% 2.41/2.64  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('89', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['87', '88'])).
% 2.41/2.64  thf('90', plain,
% 2.41/2.64      ((~ (m1_connsp_2 @ 
% 2.41/2.64           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 2.41/2.64        | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)
% 2.41/2.64        | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('91', plain,
% 2.41/2.64      ((~ (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))
% 2.41/2.64         <= (~ ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('split', [status(esa)], ['90'])).
% 2.41/2.64  thf('92', plain,
% 2.41/2.64      (~
% 2.41/2.64       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B)) | 
% 2.41/2.64       ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 2.41/2.64      inference('sup-', [status(thm)], ['89', '91'])).
% 2.41/2.64  thf('93', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1))))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['20', '21'])).
% 2.41/2.64  thf('94', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('95', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('96', plain,
% 2.41/2.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.41/2.64         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 2.41/2.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 2.41/2.64      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 2.41/2.64  thf('97', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 2.41/2.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['95', '96'])).
% 2.41/2.64  thf('98', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('99', plain,
% 2.41/2.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.41/2.64         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 2.41/2.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.41/2.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.41/2.64  thf('100', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_C))),
% 2.41/2.64      inference('sup-', [status(thm)], ['98', '99'])).
% 2.41/2.64  thf('101', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 2.41/2.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['97', '100'])).
% 2.41/2.64  thf('102', plain,
% 2.41/2.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ (k1_tops_1 @ X15 @ X14) @ 
% 2.41/2.64              (k1_tops_1 @ X15 @ X16))
% 2.41/2.64              = (k1_tops_1 @ X15 @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ X15) @ X14 @ X16)))
% 2.41/2.64          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.64          | ~ (l1_pre_topc @ X15)
% 2.41/2.64          | ~ (v2_pre_topc @ X15))),
% 2.41/2.64      inference('cnf', [status(esa)], [t46_tops_1])).
% 2.41/2.64  thf('103', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ X1))
% 2.41/2.64              = (k1_tops_1 @ sk_A @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64                  (k3_xboole_0 @ X0 @ sk_C) @ X1))))),
% 2.41/2.64      inference('sup-', [status(thm)], ['101', '102'])).
% 2.41/2.64  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('106', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ X1))
% 2.41/2.64              = (k1_tops_1 @ sk_A @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64                  (k3_xboole_0 @ X0 @ sk_C) @ X1))))),
% 2.41/2.64      inference('demod', [status(thm)], ['103', '104', '105'])).
% 2.41/2.64  thf('107', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64           = (k1_tops_1 @ sk_A @ 
% 2.41/2.64              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.41/2.64               (k3_xboole_0 @ X0 @ sk_C) @ sk_C)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['94', '106'])).
% 2.41/2.64  thf('108', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('109', plain,
% 2.41/2.64      (![X12 : $i, X13 : $i]:
% 2.41/2.64         (~ (l1_pre_topc @ X12)
% 2.41/2.64          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 2.41/2.64          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 2.41/2.64             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 2.41/2.64      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.41/2.64  thf('110', plain,
% 2.41/2.64      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.41/2.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64        | ~ (l1_pre_topc @ sk_A))),
% 2.41/2.64      inference('sup-', [status(thm)], ['108', '109'])).
% 2.41/2.64  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('112', plain,
% 2.41/2.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.41/2.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['110', '111'])).
% 2.41/2.64  thf('113', plain,
% 2.41/2.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.41/2.64         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 2.41/2.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.41/2.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.41/2.64  thf('114', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64           = (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['112', '113'])).
% 2.41/2.64  thf('115', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 2.41/2.64      inference('clc', [status(thm)], ['39', '40'])).
% 2.41/2.64  thf('116', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_C))),
% 2.41/2.64      inference('sup-', [status(thm)], ['98', '99'])).
% 2.41/2.64  thf('117', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 2.41/2.64      inference('clc', [status(thm)], ['39', '40'])).
% 2.41/2.64  thf('118', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((k3_xboole_0 @ X0 @ X1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.64      inference('sup+', [status(thm)], ['60', '72'])).
% 2.41/2.64  thf('119', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)))
% 2.41/2.64           = (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))),
% 2.41/2.64      inference('demod', [status(thm)],
% 2.41/2.64                ['107', '114', '115', '116', '117', '118'])).
% 2.41/2.64  thf('120', plain,
% 2.41/2.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.41/2.64         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.41/2.64      inference('simplify', [status(thm)], ['31'])).
% 2.41/2.64  thf('121', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         (~ (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))
% 2.41/2.64          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['119', '120'])).
% 2.41/2.64  thf('122', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['93', '121'])).
% 2.41/2.64  thf('123', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('124', plain,
% 2.41/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.41/2.64          | ~ (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 2.41/2.64          | (m1_connsp_2 @ X19 @ X18 @ X17)
% 2.41/2.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.41/2.64          | ~ (l1_pre_topc @ X18)
% 2.41/2.64          | ~ (v2_pre_topc @ X18)
% 2.41/2.64          | (v2_struct_0 @ X18))),
% 2.41/2.64      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.41/2.64  thf('125', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | ~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['123', '124'])).
% 2.41/2.64  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('128', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['125', '126', '127'])).
% 2.41/2.64  thf('129', plain,
% 2.41/2.64      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.41/2.64         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 2.41/2.64         | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['122', '128'])).
% 2.41/2.64  thf('130', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('131', plain,
% 2.41/2.64      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('demod', [status(thm)], ['129', '130'])).
% 2.41/2.64  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('133', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['131', '132'])).
% 2.41/2.64  thf('134', plain,
% 2.41/2.64      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 2.41/2.64         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 2.41/2.64      inference('split', [status(esa)], ['90'])).
% 2.41/2.64  thf('135', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 2.41/2.64       ~
% 2.41/2.64       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B))),
% 2.41/2.64      inference('sup-', [status(thm)], ['133', '134'])).
% 2.41/2.64  thf('136', plain,
% 2.41/2.64      (~
% 2.41/2.64       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B)) | 
% 2.41/2.64       ~ ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)) | 
% 2.41/2.64       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 2.41/2.64      inference('split', [status(esa)], ['90'])).
% 2.41/2.64  thf('137', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('138', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('139', plain,
% 2.41/2.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ X15) @ (k1_tops_1 @ X15 @ X14) @ 
% 2.41/2.64              (k1_tops_1 @ X15 @ X16))
% 2.41/2.64              = (k1_tops_1 @ X15 @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ X15) @ X14 @ X16)))
% 2.41/2.64          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.41/2.64          | ~ (l1_pre_topc @ X15)
% 2.41/2.64          | ~ (v2_pre_topc @ X15))),
% 2.41/2.64      inference('cnf', [status(esa)], [t46_tops_1])).
% 2.41/2.64  thf('140', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ X0))
% 2.41/2.64              = (k1_tops_1 @ sk_A @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 2.41/2.64      inference('sup-', [status(thm)], ['138', '139'])).
% 2.41/2.64  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('143', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.41/2.64          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.41/2.64              (k1_tops_1 @ sk_A @ X0))
% 2.41/2.64              = (k1_tops_1 @ sk_A @ 
% 2.41/2.64                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 2.41/2.64      inference('demod', [status(thm)], ['140', '141', '142'])).
% 2.41/2.64  thf('144', plain,
% 2.41/2.64      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 2.41/2.64         (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64         = (k1_tops_1 @ sk_A @ 
% 2.41/2.64            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['137', '143'])).
% 2.41/2.64  thf('145', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.41/2.64           (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64           = (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['54', '55'])).
% 2.41/2.64  thf('146', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['2', '3'])).
% 2.41/2.64  thf('147', plain,
% 2.41/2.64      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64         = (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))),
% 2.41/2.64      inference('demod', [status(thm)], ['144', '145', '146'])).
% 2.41/2.64  thf('148', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 2.41/2.64      inference('split', [status(esa)], ['5'])).
% 2.41/2.64  thf('149', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('150', plain,
% 2.41/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.41/2.64          | ~ (m1_connsp_2 @ X19 @ X18 @ X17)
% 2.41/2.64          | (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 2.41/2.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.41/2.64          | ~ (l1_pre_topc @ X18)
% 2.41/2.64          | ~ (v2_pre_topc @ X18)
% 2.41/2.64          | (v2_struct_0 @ X18))),
% 2.41/2.64      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.41/2.64  thf('151', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | ~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['149', '150'])).
% 2.41/2.64  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('154', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['151', '152', '153'])).
% 2.41/2.64  thf('155', plain,
% 2.41/2.64      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.41/2.64         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 2.41/2.64         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['148', '154'])).
% 2.41/2.64  thf('156', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('157', plain,
% 2.41/2.64      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 2.41/2.64      inference('demod', [status(thm)], ['155', '156'])).
% 2.41/2.64  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('159', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['157', '158'])).
% 2.41/2.64  thf('160', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('split', [status(esa)], ['0'])).
% 2.41/2.64  thf('161', plain,
% 2.41/2.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('162', plain,
% 2.41/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.41/2.64          | ~ (m1_connsp_2 @ X19 @ X18 @ X17)
% 2.41/2.64          | (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 2.41/2.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.41/2.64          | ~ (l1_pre_topc @ X18)
% 2.41/2.64          | ~ (v2_pre_topc @ X18)
% 2.41/2.64          | (v2_struct_0 @ X18))),
% 2.41/2.64      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.41/2.64  thf('163', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | ~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64          | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['161', '162'])).
% 2.41/2.64  thf('164', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('166', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64          | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 2.41/2.64          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['163', '164', '165'])).
% 2.41/2.64  thf('167', plain,
% 2.41/2.64      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.41/2.64         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['160', '166'])).
% 2.41/2.64  thf('168', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('169', plain,
% 2.41/2.64      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))
% 2.41/2.64         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('demod', [status(thm)], ['167', '168'])).
% 2.41/2.64  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('171', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1)))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['169', '170'])).
% 2.41/2.64  thf('172', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.64         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 2.41/2.64          | ~ (r2_hidden @ X0 @ X2)
% 2.41/2.64          | ~ (r2_hidden @ X0 @ X1))),
% 2.41/2.64      inference('simplify', [status(thm)], ['25'])).
% 2.41/2.64  thf('173', plain,
% 2.41/2.64      ((![X0 : $i]:
% 2.41/2.64          (~ (r2_hidden @ sk_B @ X0)
% 2.41/2.64           | (r2_hidden @ sk_B @ 
% 2.41/2.64              (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['171', '172'])).
% 2.41/2.64  thf('174', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ 
% 2.41/2.64         (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_D_1))))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 2.41/2.64             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['159', '173'])).
% 2.41/2.64  thf('175', plain,
% 2.41/2.64      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1))))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 2.41/2.64             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('sup+', [status(thm)], ['147', '174'])).
% 2.41/2.64  thf('176', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_D_1) @ 
% 2.41/2.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['10', '11'])).
% 2.41/2.64  thf('177', plain,
% 2.41/2.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.41/2.64         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 2.41/2.64          | ~ (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 2.41/2.64          | (m1_connsp_2 @ X19 @ X18 @ X17)
% 2.41/2.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.41/2.64          | ~ (l1_pre_topc @ X18)
% 2.41/2.64          | ~ (v2_pre_topc @ X18)
% 2.41/2.64          | (v2_struct_0 @ X18))),
% 2.41/2.64      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.41/2.64  thf('178', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | ~ (v2_pre_topc @ sk_A)
% 2.41/2.64          | ~ (l1_pre_topc @ sk_A)
% 2.41/2.64          | (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_D_1) @ sk_A @ X1)
% 2.41/2.64          | ~ (r2_hidden @ X1 @ 
% 2.41/2.64               (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 2.41/2.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['176', '177'])).
% 2.41/2.64  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('181', plain,
% 2.41/2.64      (![X0 : $i, X1 : $i]:
% 2.41/2.64         ((v2_struct_0 @ sk_A)
% 2.41/2.64          | (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_D_1) @ sk_A @ X1)
% 2.41/2.64          | ~ (r2_hidden @ X1 @ 
% 2.41/2.64               (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 2.41/2.64          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.41/2.64      inference('demod', [status(thm)], ['178', '179', '180'])).
% 2.41/2.64  thf('182', plain,
% 2.41/2.64      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 2.41/2.64         | (m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 2.41/2.64         | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 2.41/2.64             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['175', '181'])).
% 2.41/2.64  thf('183', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('184', plain,
% 2.41/2.64      ((((m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 2.41/2.64         | (v2_struct_0 @ sk_A)))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 2.41/2.64             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('demod', [status(thm)], ['182', '183'])).
% 2.41/2.64  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 2.41/2.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.64  thf('186', plain,
% 2.41/2.64      (((m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 2.41/2.64         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 2.41/2.64             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 2.41/2.64      inference('clc', [status(thm)], ['184', '185'])).
% 2.41/2.64  thf('187', plain,
% 2.41/2.64      (![X0 : $i]:
% 2.41/2.64         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 2.41/2.64           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 2.41/2.64      inference('sup-', [status(thm)], ['2', '3'])).
% 2.41/2.64  thf('188', plain,
% 2.41/2.64      ((~ (m1_connsp_2 @ 
% 2.41/2.64           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 2.41/2.64         <= (~
% 2.41/2.64             ((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('split', [status(esa)], ['90'])).
% 2.41/2.64  thf('189', plain,
% 2.41/2.64      ((~ (m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 2.41/2.64         <= (~
% 2.41/2.64             ((m1_connsp_2 @ 
% 2.41/2.64               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 2.41/2.64               sk_B)))),
% 2.41/2.64      inference('sup-', [status(thm)], ['187', '188'])).
% 2.41/2.64  thf('190', plain,
% 2.41/2.64      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B)) | 
% 2.41/2.64       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 2.41/2.64       ~ ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 2.41/2.64      inference('sup-', [status(thm)], ['186', '189'])).
% 2.41/2.64  thf('191', plain,
% 2.41/2.64      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 2.41/2.64       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 2.41/2.64         sk_A @ sk_B))),
% 2.41/2.64      inference('split', [status(esa)], ['5'])).
% 2.41/2.64  thf('192', plain, ($false),
% 2.41/2.64      inference('sat_resolution*', [status(thm)],
% 2.41/2.64                ['1', '92', '135', '136', '190', '191'])).
% 2.41/2.64  
% 2.41/2.64  % SZS output end Refutation
% 2.41/2.64  
% 2.41/2.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
