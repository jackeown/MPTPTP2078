%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v66dnFdIYL

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 143 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  697 (1796 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t65_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( m1_pre_topc @ A @ B )
            <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_pre_topc])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t31_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( l1_pre_topc @ C )
             => ! [D: $i] :
                  ( ( l1_pre_topc @ D )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( m1_pre_topc @ D @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ( m1_pre_topc @ X7 @ X6 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X2 @ X1 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
   <= ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_B )
   <= ~ ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','26'])).

thf('28',plain,(
    ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('29',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
   <= ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','26','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( m1_pre_topc @ X2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['28','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v66dnFdIYL
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 39 iterations in 0.029s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(t65_pre_topc, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( l1_pre_topc @ B ) =>
% 0.20/0.52           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.52             ( m1_pre_topc @
% 0.20/0.52               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( l1_pre_topc @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( l1_pre_topc @ B ) =>
% 0.20/0.52              ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.52                ( m1_pre_topc @
% 0.20/0.52                  A @ 
% 0.20/0.52                  ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t65_pre_topc])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (m1_pre_topc @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (m1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (m1_pre_topc @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m1_pre_topc @ sk_A @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((m1_pre_topc @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.20/0.52       ~ ((m1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | (m1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.20/0.52         <= (((m1_pre_topc @ sk_A @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf(dt_u1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( u1_pre_topc @ A ) @ 
% 0.20/0.52         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X5 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.52          | ~ (l1_pre_topc @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf(dt_g1_pre_topc, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.20/0.52         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X5 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.20/0.52          | ~ (l1_pre_topc @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ( v1_pre_topc @ A ) =>
% 0.20/0.52         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_pre_topc @ X0)
% 0.20/0.52          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.52  thf(t31_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( l1_pre_topc @ B ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( l1_pre_topc @ C ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( l1_pre_topc @ D ) =>
% 0.20/0.52                   ( ( ( ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.52                       ( ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.20/0.52                         ( g1_pre_topc @
% 0.20/0.52                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.20/0.52                       ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X6)
% 0.20/0.52          | ~ (l1_pre_topc @ X7)
% 0.20/0.52          | (m1_pre_topc @ X7 @ X6)
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8))
% 0.20/0.52              != (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.20/0.52          | ~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.20/0.52              != (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.20/0.52          | ~ (l1_pre_topc @ X8)
% 0.20/0.52          | ~ (l1_pre_topc @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.52              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (m1_pre_topc @ X1 @ X2)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('eq_res', [status(thm)], ['12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X2)
% 0.20/0.52          | (m1_pre_topc @ X1 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.52              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X1)
% 0.20/0.52          | (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.20/0.52          | ~ (l1_pre_topc @ X2)
% 0.20/0.52          | ~ (v1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | (m1_pre_topc @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (m1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.52         <= (((m1_pre_topc @ sk_A @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '20'])).
% 0.20/0.52  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_A @ sk_B))
% 0.20/0.52         <= (((m1_pre_topc @ sk_A @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((~ (m1_pre_topc @ sk_A @ sk_B)) <= (~ ((m1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_A @ sk_B)) | 
% 0.20/0.52       ~
% 0.20/0.52       ((m1_pre_topc @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((m1_pre_topc @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (~ (m1_pre_topc @ sk_A @ 
% 0.20/0.52          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_A @ sk_B)) <= (((m1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_A @ sk_B)) | 
% 0.20/0.52       ((m1_pre_topc @ sk_A @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('31', plain, (((m1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['2', '26', '30'])).
% 0.20/0.52  thf('32', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (l1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v1_pre_topc @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_pre_topc @ X0)
% 0.20/0.52          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X2)
% 0.20/0.52          | (m1_pre_topc @ X1 @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.52              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (v1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X2)
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | (m1_pre_topc @ X2 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X2 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.20/0.52          | ~ (m1_pre_topc @ X2 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X2)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (v1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (m1_pre_topc @ X1 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X1 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ 
% 0.20/0.52               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | (m1_pre_topc @ X1 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X1 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_pre_topc @ sk_A @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '42'])).
% 0.20/0.52  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((m1_pre_topc @ sk_A @ 
% 0.20/0.52        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.52  thf('47', plain, ($false), inference('demod', [status(thm)], ['28', '46'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
