%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WbRplvPDhc

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:08 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 191 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  737 (2536 expanded)
%              Number of equality atoms :   49 ( 117 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_pre_topc @ X23 @ X24 ) ) )
        = ( k2_pre_topc @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('23',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','14','21','22','23'])).

thf('25',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X11 @ X9 )
        = ( k9_subset_1 @ X10 @ X11 @ ( k3_subset_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X1 @ k1_xboole_0 )
        = ( k9_subset_1 @ X0 @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ k1_xboole_0 )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k7_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X16: $i] :
      ( ( ( k1_struct_0 @ X16 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('43',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_struct_0 @ X19 ) ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('47',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('50',plain,
    ( sk_C
    = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39','40','47','48','49'])).

thf('51',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','31','50'])).

thf('52',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
     != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('60',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WbRplvPDhc
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 170 iterations in 0.071s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.35/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(t81_tops_1, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( v1_tops_1 @ B @ A ) =>
% 0.35/0.53             ( ![C:$i]:
% 0.35/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                 ( ( v3_pre_topc @ C @ A ) =>
% 0.35/0.53                   ( ( k2_pre_topc @ A @ C ) =
% 0.35/0.53                     ( k2_pre_topc @
% 0.35/0.53                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53              ( ( v1_tops_1 @ B @ A ) =>
% 0.35/0.53                ( ![C:$i]:
% 0.35/0.53                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                    ( ( v3_pre_topc @ C @ A ) =>
% 0.35/0.53                      ( ( k2_pre_topc @ A @ C ) =
% 0.35/0.53                        ( k2_pre_topc @
% 0.35/0.53                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t41_tops_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53               ( ( v3_pre_topc @ B @ A ) =>
% 0.35/0.53                 ( ( k2_pre_topc @
% 0.35/0.53                     A @ 
% 0.35/0.53                     ( k9_subset_1 @
% 0.35/0.53                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.35/0.53                   ( k2_pre_topc @
% 0.35/0.53                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.53          | ~ (v3_pre_topc @ X22 @ X23)
% 0.35/0.53          | ((k2_pre_topc @ X23 @ 
% 0.35/0.53              (k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.35/0.53               (k2_pre_topc @ X23 @ X24)))
% 0.35/0.53              = (k2_pre_topc @ X23 @ 
% 0.35/0.53                 (k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ X24)))
% 0.35/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.53          | ~ (l1_pre_topc @ X23)
% 0.35/0.53          | ~ (v2_pre_topc @ X23))),
% 0.35/0.53      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v2_pre_topc @ sk_A)
% 0.35/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | ((k2_pre_topc @ sk_A @ 
% 0.35/0.53              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.35/0.53               (k2_pre_topc @ sk_A @ X0)))
% 0.35/0.53              = (k2_pre_topc @ sk_A @ 
% 0.35/0.53                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.35/0.53          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(d3_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X17 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(commutativity_k9_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.35/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.53           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.53            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 0.35/0.53          | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.35/0.53  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_l1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.53  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.53           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['10', '13'])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X17 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.35/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.53  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.35/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.53           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.53           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['10', '13'])).
% 0.35/0.53  thf('23', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | ((k2_pre_topc @ sk_A @ 
% 0.35/0.53              (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ 
% 0.35/0.53               (k2_pre_topc @ sk_A @ X0)))
% 0.35/0.53              = (k2_pre_topc @ sk_A @ 
% 0.35/0.53                 (k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C))))),
% 0.35/0.53      inference('demod', [status(thm)], ['3', '4', '5', '14', '21', '22', '23'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (((k2_pre_topc @ sk_A @ 
% 0.35/0.53         (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ 
% 0.35/0.53          (k2_pre_topc @ sk_A @ sk_B)))
% 0.35/0.53         = (k2_pre_topc @ sk_A @ 
% 0.35/0.53            (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(d3_tops_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.35/0.53             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.35/0.53          | ~ (v1_tops_1 @ X20 @ X21)
% 0.35/0.53          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.35/0.53          | ~ (l1_pre_topc @ X21))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.35/0.53        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('30', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('31', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t4_subset_1, axiom,
% 0.35/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.53  thf(t32_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ![C:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.35/0.53             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.35/0.53          | ((k7_subset_1 @ X10 @ X11 @ X9)
% 0.35/0.53              = (k9_subset_1 @ X10 @ X11 @ (k3_subset_1 @ X10 @ X9)))
% 0.35/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.35/0.53          | ((k7_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.35/0.53              = (k9_subset_1 @ X0 @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ k1_xboole_0)
% 0.35/0.53         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.35/0.53            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k7_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.35/0.54          | ((k7_subset_1 @ X7 @ X6 @ X8) = (k4_xboole_0 @ X6 @ X8)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.35/0.54           = (k4_xboole_0 @ sk_C @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf(t3_boole, axiom,
% 0.35/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.54  thf('40', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.35/0.54  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.54  thf(d2_struct_0, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         (((k1_struct_0 @ X16) = (k1_xboole_0)) | ~ (l1_struct_0 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.35/0.54  thf('43', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.54  thf(t27_pre_topc, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_struct_0 @ A ) =>
% 0.35/0.54       ( ( k2_struct_0 @ A ) =
% 0.35/0.54         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (![X19 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X19)
% 0.35/0.54            = (k3_subset_1 @ (u1_struct_0 @ X19) @ (k1_struct_0 @ X19)))
% 0.35/0.54          | ~ (l1_struct_0 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      ((((k2_struct_0 @ sk_A)
% 0.35/0.54          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup+', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (((k2_struct_0 @ sk_A)
% 0.35/0.54         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '13'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.35/0.54           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      (((sk_C)
% 0.35/0.54         = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['36', '39', '40', '47', '48', '49'])).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_C)
% 0.35/0.54         = (k2_pre_topc @ sk_A @ 
% 0.35/0.54            (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.35/0.54      inference('demod', [status(thm)], ['25', '31', '50'])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      (![X17 : $i]:
% 0.35/0.54         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_C)
% 0.35/0.54         != (k2_pre_topc @ sk_A @ 
% 0.35/0.54             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.54         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.35/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.35/0.54      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.35/0.54  thf('56', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.35/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_C)
% 0.35/0.54         != (k2_pre_topc @ sk_A @ 
% 0.35/0.54             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.35/0.54      inference('demod', [status(thm)], ['53', '56'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((((k2_pre_topc @ sk_A @ sk_C)
% 0.35/0.54          != (k2_pre_topc @ sk_A @ 
% 0.35/0.54              (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C)))
% 0.35/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['52', '57'])).
% 0.35/0.54  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (((k2_pre_topc @ sk_A @ sk_C)
% 0.35/0.54         != (k2_pre_topc @ sk_A @ 
% 0.35/0.54             (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.35/0.54      inference('demod', [status(thm)], ['58', '59'])).
% 0.35/0.54  thf('61', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['51', '60'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
