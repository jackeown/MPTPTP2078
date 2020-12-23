%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dl0Kbqy4bh

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 226 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          : 1351 (3186 expanded)
%              Number of equality atoms :   89 ( 178 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('34',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('49',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ~ ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) )
    | ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('56',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference(simpl_trail,[status(thm)],['49','56'])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( sk_B != sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('67',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('70',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(split,[status(esa)],['69'])).

thf('73',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ~ ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) )
    | ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(split,[status(esa)],['69'])).

thf('78',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 ) ) ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 ) ) ),
    inference(simpl_trail,[status(thm)],['70','78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('85',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('89',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['83','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','65','66','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dl0Kbqy4bh
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 214 iterations in 0.084s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.54  thf(t76_tops_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54               ( k7_subset_1 @
% 0.21/0.54                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54                  ( k7_subset_1 @
% 0.21/0.54                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.54       ~
% 0.21/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t74_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.54             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X33 : $i, X34 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.21/0.54          | ((k1_tops_1 @ X34 @ X33)
% 0.21/0.54              = (k7_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.21/0.54                 (k2_tops_1 @ X34 @ X33)))
% 0.21/0.54          | ~ (l1_pre_topc @ X34))),
% 0.21/0.54      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.21/0.54          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.54           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.54         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.21/0.54  thf(d4_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.54  thf(t3_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.54  thf('12', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf(d5_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.54          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.54          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.54          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.54  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('condensation', [status(thm)], ['15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.54          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k2_pre_topc, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X25)
% 0.21/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.54          | (m1_subset_1 @ (k2_pre_topc @ X25 @ X26) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.21/0.54          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.54           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.21/0.54        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['24', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.54          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.54           | ~ (r2_hidden @ 
% 0.21/0.54                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((((r2_hidden @ 
% 0.21/0.54          (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ k1_xboole_0)
% 0.21/0.54         | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.54         | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.54         | (r2_hidden @ 
% 0.21/0.54            (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.54            k1_xboole_0)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.54  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('condensation', [status(thm)], ['15'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf(t100_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X15 @ X16)
% 0.21/0.54           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.54          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('eq_fact', [status(thm)], ['37'])).
% 0.21/0.54  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('condensation', [status(thm)], ['15'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X15 @ X16)
% 0.21/0.54           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.54  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['36', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['9', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t55_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( l1_pre_topc @ B ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.54                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.54                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.54                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54          | (v3_pre_topc @ X31 @ X32)
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)
% 0.21/0.54           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54           | (v3_pre_topc @ X31 @ X32)))
% 0.21/0.54         <= ((![X31 : $i, X32 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54                 | ~ (l1_pre_topc @ X32)
% 0.21/0.54                 | ~ (v2_pre_topc @ X32)
% 0.21/0.54                 | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54                 | (v3_pre_topc @ X31 @ X32))))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))
% 0.21/0.54         <= ((![X29 : $i, X30 : $i]:
% 0.21/0.54                (~ (l1_pre_topc @ X29)
% 0.21/0.54                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.54         <= ((![X29 : $i, X30 : $i]:
% 0.21/0.54                (~ (l1_pre_topc @ X29)
% 0.21/0.54                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)
% 0.21/0.54           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54           | (v3_pre_topc @ X31 @ X32))) | 
% 0.21/0.54       (![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)
% 0.21/0.54           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54           | (v3_pre_topc @ X31 @ X32)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32)
% 0.21/0.54          | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.21/0.54          | (v3_pre_topc @ X31 @ X32))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['49', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A)
% 0.21/0.54        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '57'])).
% 0.21/0.54  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (((((sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A)))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A))
% 0.21/0.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.54       ~
% 0.21/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.54       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['25'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['25'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54          | ((k1_tops_1 @ X29 @ X30) = (X30))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54          | ~ (l1_pre_topc @ X32)
% 0.21/0.54          | ~ (v2_pre_topc @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54           | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54           | ((k1_tops_1 @ X29 @ X30) = (X30))))
% 0.21/0.54         <= ((![X29 : $i, X30 : $i]:
% 0.21/0.54                (~ (l1_pre_topc @ X29)
% 0.21/0.54                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54                 | ((k1_tops_1 @ X29 @ X30) = (X30)))))),
% 0.21/0.54      inference('split', [status(esa)], ['69'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)))
% 0.21/0.54         <= ((![X31 : $i, X32 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54                 | ~ (l1_pre_topc @ X32)
% 0.21/0.54                 | ~ (v2_pre_topc @ X32))))),
% 0.21/0.54      inference('split', [status(esa)], ['69'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.54         <= ((![X31 : $i, X32 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54                 | ~ (l1_pre_topc @ X32)
% 0.21/0.54                 | ~ (v2_pre_topc @ X32))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.54  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)))),
% 0.21/0.54      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54           | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54           | ((k1_tops_1 @ X29 @ X30) = (X30)))) | 
% 0.21/0.54       (![X31 : $i, X32 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.21/0.54           | ~ (l1_pre_topc @ X32)
% 0.21/0.54           | ~ (v2_pre_topc @ X32)))),
% 0.21/0.54      inference('split', [status(esa)], ['69'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((![X29 : $i, X30 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ X29)
% 0.21/0.54           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54           | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54           | ((k1_tops_1 @ X29 @ X30) = (X30))))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ~ (v3_pre_topc @ X30 @ X29)
% 0.21/0.54          | ((k1_tops_1 @ X29 @ X30) = (X30)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['70', '78'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.21/0.54        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['68', '79'])).
% 0.21/0.54  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.54         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '82'])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l78_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54             ( k7_subset_1 @
% 0.21/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | ((k2_tops_1 @ X28 @ X27)
% 0.21/0.54              = (k7_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.21/0.54                 (k2_pre_topc @ X28 @ X27) @ (k1_tops_1 @ X28 @ X27)))
% 0.21/0.54          | ~ (l1_pre_topc @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.21/0.55  thf('90', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['83', '89'])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('92', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('93', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.21/0.55             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['90', '93'])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['94'])).
% 0.21/0.55  thf('96', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '65', '66', '95'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
