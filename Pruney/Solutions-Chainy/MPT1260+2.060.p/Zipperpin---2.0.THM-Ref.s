%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wwP368smk

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:32 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 490 expanded)
%              Number of leaves         :   30 ( 152 expanded)
%              Depth                    :   23
%              Number of atoms          : 1617 (6170 expanded)
%              Number of equality atoms :  116 ( 406 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != X30 )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('2',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 )
        | ( ( k1_tops_1 @ X31 @ X30 )
         != X30 )
        | ( v3_pre_topc @ X30 @ X31 ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 )
        | ( ( k1_tops_1 @ X31 @ X30 )
         != X30 )
        | ( v3_pre_topc @ X30 @ X31 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
   <= ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 )
        | ( ( k1_tops_1 @ X31 @ X30 )
         != X30 )
        | ( v3_pre_topc @ X30 @ X31 ) )
    | ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != X30 )
      | ( v3_pre_topc @ X30 @ X31 ) ) ),
    inference('sat_resolution*',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != X30 )
      | ( v3_pre_topc @ X30 @ X31 ) ) ),
    inference(simpl_trail,[status(thm)],['2','9'])).

thf('11',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k1_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('40',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','40'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('67',plain,
    ( ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( v3_pre_topc @ X29 @ X28 )
        | ( ( k1_tops_1 @ X28 @ X29 )
          = X29 ) )
   <= ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( v3_pre_topc @ X29 @ X28 )
        | ( ( k1_tops_1 @ X28 @ X29 )
          = X29 ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(split,[status(esa)],['66'])).

thf('70',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ! [X28: $i,X29: $i] :
        ( ~ ( l1_pre_topc @ X28 )
        | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
        | ~ ( v3_pre_topc @ X29 @ X28 )
        | ( ( k1_tops_1 @ X28 @ X29 )
          = X29 ) )
    | ! [X30: $i,X31: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
        | ~ ( l1_pre_topc @ X31 )
        | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(split,[status(esa)],['66'])).

thf('75',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X29 )
        = X29 ) ) ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X29 )
        = X29 ) ) ),
    inference(simpl_trail,[status(thm)],['67','75'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('82',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ X26 ) @ ( k1_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('86',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['62'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('94',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['63','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['61','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','95'])).

thf('97',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','96'])).

thf('98',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
     != sk_B ) ),
    inference(demod,[status(thm)],['14','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('104',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['63','92'])).

thf('105',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,(
    ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
 != sk_B ),
    inference(clc,[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['112'])).

thf('114',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['116','118'])).

thf('120',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('125',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['123','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','126'])).

thf('128',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('131',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['116','118'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['129','132','133'])).

thf('135',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['106','134'])).

thf('136',plain,(
    $false ),
    inference(simplify,[status(thm)],['135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wwP368smk
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 351 iterations in 0.217s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(t76_tops_1, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.68             ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.68               ( k7_subset_1 @
% 0.46/0.68                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68          ( ![B:$i]:
% 0.46/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68              ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.68                ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.68                  ( k7_subset_1 @
% 0.46/0.68                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t55_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( l1_pre_topc @ B ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68               ( ![D:$i]:
% 0.46/0.68                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.68                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.46/0.68                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.46/0.68                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.46/0.68                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X28)
% 0.46/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68          | ((k1_tops_1 @ X31 @ X30) != (X30))
% 0.46/0.68          | (v3_pre_topc @ X30 @ X31)
% 0.46/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68          | ~ (l1_pre_topc @ X31)
% 0.46/0.68          | ~ (v2_pre_topc @ X31))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      ((![X30 : $i, X31 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68           | ~ (l1_pre_topc @ X31)
% 0.46/0.68           | ~ (v2_pre_topc @ X31)
% 0.46/0.68           | ((k1_tops_1 @ X31 @ X30) != (X30))
% 0.46/0.68           | (v3_pre_topc @ X30 @ X31)))
% 0.46/0.68         <= ((![X30 : $i, X31 : $i]:
% 0.46/0.68                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68                 | ~ (l1_pre_topc @ X31)
% 0.46/0.68                 | ~ (v2_pre_topc @ X31)
% 0.46/0.68                 | ((k1_tops_1 @ X31 @ X30) != (X30))
% 0.46/0.68                 | (v3_pre_topc @ X30 @ X31))))),
% 0.46/0.68      inference('split', [status(esa)], ['1'])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      ((![X28 : $i, X29 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X28)
% 0.46/0.68           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))))
% 0.46/0.68         <= ((![X28 : $i, X29 : $i]:
% 0.46/0.68                (~ (l1_pre_topc @ X28)
% 0.46/0.68                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))))),
% 0.46/0.68      inference('split', [status(esa)], ['1'])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A))
% 0.46/0.68         <= ((![X28 : $i, X29 : $i]:
% 0.46/0.68                (~ (l1_pre_topc @ X28)
% 0.46/0.68                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (~
% 0.46/0.68       (![X28 : $i, X29 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X28)
% 0.46/0.68           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))))),
% 0.46/0.68      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      ((![X30 : $i, X31 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68           | ~ (l1_pre_topc @ X31)
% 0.46/0.68           | ~ (v2_pre_topc @ X31)
% 0.46/0.68           | ((k1_tops_1 @ X31 @ X30) != (X30))
% 0.46/0.68           | (v3_pre_topc @ X30 @ X31))) | 
% 0.46/0.68       (![X28 : $i, X29 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X28)
% 0.46/0.68           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))))),
% 0.46/0.68      inference('split', [status(esa)], ['1'])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      ((![X30 : $i, X31 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68           | ~ (l1_pre_topc @ X31)
% 0.46/0.68           | ~ (v2_pre_topc @ X31)
% 0.46/0.68           | ((k1_tops_1 @ X31 @ X30) != (X30))
% 0.46/0.68           | (v3_pre_topc @ X30 @ X31)))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X30 : $i, X31 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68          | ~ (l1_pre_topc @ X31)
% 0.46/0.68          | ~ (v2_pre_topc @ X31)
% 0.46/0.68          | ((k1_tops_1 @ X31 @ X30) != (X30))
% 0.46/0.68          | (v3_pre_topc @ X30 @ X31))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['2', '9'])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_B @ sk_A)
% 0.46/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.46/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '10'])).
% 0.46/0.68  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t74_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( k1_tops_1 @ A @ B ) =
% 0.46/0.68             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X32 : $i, X33 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.46/0.68          | ((k1_tops_1 @ X33 @ X32)
% 0.46/0.68              = (k7_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.46/0.68                 (k2_tops_1 @ X33 @ X32)))
% 0.46/0.68          | ~ (l1_pre_topc @ X33))),
% 0.46/0.68      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.68               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.68  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.46/0.68          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.68         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.46/0.68  thf(t48_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.68           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.68         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf(t100_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X14 @ X15)
% 0.46/0.68           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.46/0.68            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.68         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.46/0.68            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.68  thf(d4_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.68       ( ![D:$i]:
% 0.46/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf(t2_boole, axiom,
% 0.46/0.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X14 @ X15)
% 0.46/0.68           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.68           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.68           (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.68           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['34', '40'])).
% 0.46/0.68  thf(d5_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.68       ( ![D:$i]:
% 0.46/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X12 @ X11)
% 0.46/0.68          | ~ (r2_hidden @ X12 @ X10)
% 0.46/0.68          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X12 @ X10)
% 0.46/0.68          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['41', '43'])).
% 0.46/0.68  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.68      inference('condensation', [status(thm)], ['44'])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.68          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['29', '45'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.68      inference('condensation', [status(thm)], ['44'])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.68          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_k2_pre_topc, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.68       ( m1_subset_1 @
% 0.46/0.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X24)
% 0.46/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.68          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.68  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.46/0.68          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.68           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.46/0.68        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.68      inference('split', [status(esa)], ['57'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['56', '58'])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X12 @ X10)
% 0.46/0.68          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      ((![X0 : $i]:
% 0.46/0.68          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.68           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.46/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.46/0.68        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.46/0.68       ~
% 0.46/0.68       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.68      inference('split', [status(esa)], ['62'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['57'])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X28)
% 0.46/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68          | ~ (v3_pre_topc @ X29 @ X28)
% 0.46/0.68          | ((k1_tops_1 @ X28 @ X29) = (X29))
% 0.46/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68          | ~ (l1_pre_topc @ X31)
% 0.46/0.68          | ~ (v2_pre_topc @ X31))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      ((![X28 : $i, X29 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X28)
% 0.46/0.68           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68           | ~ (v3_pre_topc @ X29 @ X28)
% 0.46/0.68           | ((k1_tops_1 @ X28 @ X29) = (X29))))
% 0.46/0.68         <= ((![X28 : $i, X29 : $i]:
% 0.46/0.68                (~ (l1_pre_topc @ X28)
% 0.46/0.68                 | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X29 @ X28)
% 0.46/0.68                 | ((k1_tops_1 @ X28 @ X29) = (X29)))))),
% 0.46/0.68      inference('split', [status(esa)], ['66'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      ((![X30 : $i, X31 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68           | ~ (l1_pre_topc @ X31)
% 0.46/0.68           | ~ (v2_pre_topc @ X31)))
% 0.46/0.68         <= ((![X30 : $i, X31 : $i]:
% 0.46/0.68                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68                 | ~ (l1_pre_topc @ X31)
% 0.46/0.68                 | ~ (v2_pre_topc @ X31))))),
% 0.46/0.68      inference('split', [status(esa)], ['66'])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.68         <= ((![X30 : $i, X31 : $i]:
% 0.46/0.68                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68                 | ~ (l1_pre_topc @ X31)
% 0.46/0.68                 | ~ (v2_pre_topc @ X31))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.68  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (~
% 0.46/0.68       (![X30 : $i, X31 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68           | ~ (l1_pre_topc @ X31)
% 0.46/0.68           | ~ (v2_pre_topc @ X31)))),
% 0.46/0.68      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      ((![X28 : $i, X29 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X28)
% 0.46/0.68           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68           | ~ (v3_pre_topc @ X29 @ X28)
% 0.46/0.68           | ((k1_tops_1 @ X28 @ X29) = (X29)))) | 
% 0.46/0.68       (![X30 : $i, X31 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.68           | ~ (l1_pre_topc @ X31)
% 0.46/0.68           | ~ (v2_pre_topc @ X31)))),
% 0.46/0.68      inference('split', [status(esa)], ['66'])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      ((![X28 : $i, X29 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X28)
% 0.46/0.68           | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68           | ~ (v3_pre_topc @ X29 @ X28)
% 0.46/0.68           | ((k1_tops_1 @ X28 @ X29) = (X29))))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (![X28 : $i, X29 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X28)
% 0.46/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.68          | ~ (v3_pre_topc @ X29 @ X28)
% 0.46/0.68          | ((k1_tops_1 @ X28 @ X29) = (X29)))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['67', '75'])).
% 0.46/0.68  thf('77', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.46/0.68        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['65', '76'])).
% 0.46/0.68  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['77', '78'])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.46/0.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['64', '79'])).
% 0.46/0.68  thf('81', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(l78_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.68             ( k7_subset_1 @
% 0.46/0.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.46/0.68               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.68  thf('82', plain,
% 0.46/0.68      (![X26 : $i, X27 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.68          | ((k2_tops_1 @ X27 @ X26)
% 0.46/0.68              = (k7_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.46/0.68                 (k2_pre_topc @ X27 @ X26) @ (k1_tops_1 @ X27 @ X26)))
% 0.46/0.68          | ~ (l1_pre_topc @ X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.68  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.68           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('86', plain,
% 0.46/0.68      (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.68            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.68  thf('87', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['80', '86'])).
% 0.46/0.68  thf('88', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.68           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.68         <= (~
% 0.46/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.68      inference('split', [status(esa)], ['62'])).
% 0.46/0.68  thf('90', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.46/0.68         <= (~
% 0.46/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.68  thf('91', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.68         <= (~
% 0.46/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.46/0.68             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['87', '90'])).
% 0.46/0.68  thf('92', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.46/0.68       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.68      inference('simplify', [status(thm)], ['91'])).
% 0.46/0.68  thf('93', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.46/0.68       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['57'])).
% 0.46/0.68  thf('94', plain,
% 0.46/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['63', '92', '93'])).
% 0.46/0.68  thf('95', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.68          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['61', '94'])).
% 0.46/0.68  thf('96', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.68          | ~ (r2_hidden @ 
% 0.46/0.68               (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['49', '95'])).
% 0.46/0.68  thf('97', plain,
% 0.46/0.68      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.68        | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['46', '96'])).
% 0.46/0.68  thf('98', plain,
% 0.46/0.68      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['97'])).
% 0.46/0.68  thf('99', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.68         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('100', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['98', '99'])).
% 0.46/0.68  thf('101', plain,
% 0.46/0.68      (((k1_tops_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '100'])).
% 0.46/0.68  thf('102', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_B @ sk_A)
% 0.46/0.68        | ((k5_xboole_0 @ sk_B @ k1_xboole_0) != (sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['14', '101'])).
% 0.46/0.68  thf('103', plain,
% 0.46/0.68      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['62'])).
% 0.46/0.68  thf('104', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['63', '92'])).
% 0.46/0.68  thf('105', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 0.46/0.68  thf('106', plain, (((k5_xboole_0 @ sk_B @ k1_xboole_0) != (sk_B))),
% 0.46/0.68      inference('clc', [status(thm)], ['102', '105'])).
% 0.46/0.68  thf('107', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('108', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.68      inference('condensation', [status(thm)], ['44'])).
% 0.46/0.68  thf('109', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.46/0.68          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.68  thf('110', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('111', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.46/0.68          | ((X1) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['109', '110'])).
% 0.46/0.68  thf('112', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('113', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.46/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.68      inference('eq_fact', [status(thm)], ['112'])).
% 0.46/0.68  thf('114', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.46/0.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.46/0.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('115', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.46/0.68          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.46/0.68          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.46/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['113', '114'])).
% 0.46/0.68  thf('116', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.46/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['115'])).
% 0.46/0.68  thf('117', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.46/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.46/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('118', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.46/0.68          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('eq_fact', [status(thm)], ['117'])).
% 0.46/0.68  thf('119', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('clc', [status(thm)], ['116', '118'])).
% 0.46/0.68  thf('120', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.68           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('121', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X12 @ X10)
% 0.46/0.68          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.46/0.68  thf('122', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.68          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.68  thf('123', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X1 @ X0)
% 0.46/0.68          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['119', '122'])).
% 0.46/0.68  thf('124', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X12 @ X11)
% 0.46/0.68          | (r2_hidden @ X12 @ X9)
% 0.46/0.68          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.68  thf('125', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.46/0.68         ((r2_hidden @ X12 @ X9)
% 0.46/0.68          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['124'])).
% 0.46/0.68  thf('126', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('clc', [status(thm)], ['123', '125'])).
% 0.46/0.68  thf('127', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['111', '126'])).
% 0.46/0.68  thf('128', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.68           = (k3_xboole_0 @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('129', plain,
% 0.46/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['127', '128'])).
% 0.46/0.68  thf('130', plain,
% 0.46/0.68      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.68  thf('131', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X14 @ X15)
% 0.46/0.68           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('132', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['130', '131'])).
% 0.46/0.68  thf('133', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('clc', [status(thm)], ['116', '118'])).
% 0.46/0.68  thf('134', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['129', '132', '133'])).
% 0.46/0.68  thf('135', plain, (((sk_B) != (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['106', '134'])).
% 0.46/0.68  thf('136', plain, ($false), inference('simplify', [status(thm)], ['135'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.53/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
