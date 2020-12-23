%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1BHhkHVol4

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:40 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 197 expanded)
%              Number of leaves         :   51 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          : 1107 (2355 expanded)
%              Number of equality atoms :   55 ( 104 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t15_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ( B
              = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) )
      | ( X32 = X33 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('14',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t2_yellow19,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf('16',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) ) )
      | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ X42 ) )
      | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X42 ) ) ) )
      | ~ ( r2_hidden @ X43 @ X41 )
      | ~ ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('17',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X42 ) ) ) )
      | ~ ( v2_waybel_0 @ X41 @ ( k3_lattice3 @ ( k1_lattice3 @ X42 ) ) )
      | ~ ( v13_waybel_0 @ X41 @ ( k3_lattice3 @ ( k1_lattice3 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X42 ) ) ) ) )
      | ~ ( r2_hidden @ X43 @ X41 )
      | ~ ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','25','28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X37: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X25 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','58'])).

thf('60',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t14_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ ( k1_tarski @ k1_xboole_0 ) )
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( v2_waybel_0 @ X39 @ ( k3_yellow_1 @ ( k2_struct_0 @ X40 ) ) )
      | ~ ( v13_waybel_0 @ X39 @ ( k3_yellow_1 @ ( k2_struct_0 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X40 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X40 ) ) ) @ X39 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X40 @ ( k3_yellow19 @ X40 @ ( k2_struct_0 @ X40 ) @ X39 ) ) )
      | ~ ( l1_struct_0 @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('63',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X38: $i] :
      ( ( k3_yellow_1 @ X38 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('67',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( v2_waybel_0 @ X39 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X40 ) ) ) )
      | ~ ( v13_waybel_0 @ X39 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X40 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X40 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X40 ) ) ) ) @ X39 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X40 @ ( k3_yellow19 @ X40 @ ( k2_struct_0 @ X40 ) @ X39 ) ) )
      | ~ ( l1_struct_0 @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('71',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','80'])).

thf('82',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','81'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1BHhkHVol4
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 989 iterations in 0.618s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.10  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.91/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.91/1.10  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.91/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.91/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.91/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.10  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.10  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.91/1.10  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.91/1.10  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.91/1.10  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.91/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(t15_yellow19, conjecture,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.91/1.10             ( v1_subset_1 @
% 0.91/1.10               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.91/1.10             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.91/1.10             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.91/1.10             ( m1_subset_1 @
% 0.91/1.10               B @ 
% 0.91/1.10               ( k1_zfmisc_1 @
% 0.91/1.10                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.91/1.10           ( ( B ) =
% 0.91/1.10             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i]:
% 0.91/1.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.10          ( ![B:$i]:
% 0.91/1.10            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.91/1.10                ( v1_subset_1 @
% 0.91/1.10                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.91/1.10                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.91/1.10                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.91/1.10                ( m1_subset_1 @
% 0.91/1.10                  B @ 
% 0.91/1.10                  ( k1_zfmisc_1 @
% 0.91/1.10                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.91/1.10              ( ( B ) =
% 0.91/1.10                ( k2_yellow19 @
% 0.91/1.10                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.91/1.10  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.10  thf(t48_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X22 : $i, X23 : $i]:
% 0.91/1.10         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.91/1.10           = (k3_xboole_0 @ X22 @ X23))),
% 0.91/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.10  thf(t36_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.91/1.10      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.91/1.10      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.10      inference('sup+', [status(thm)], ['1', '4'])).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.91/1.10      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.10  thf(t3_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.10            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X9 : $i, X10 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.10  thf(t17_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( A ) != ( B ) ) =>
% 0.91/1.10       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X32 : $i, X33 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33))
% 0.91/1.10          | ((X32) = (X33)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.91/1.10  thf(l24_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X30 : $i, X31 : $i]:
% 0.91/1.10         (~ (r1_xboole_0 @ (k1_tarski @ X30) @ X31) | ~ (r2_hidden @ X30 @ X31))),
% 0.91/1.10      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.10  thf('11', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.91/1.10          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['7', '10'])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X9 : $i, X10 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(d2_yellow_1, axiom,
% 0.91/1.10    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ 
% 0.91/1.10        (k1_zfmisc_1 @ 
% 0.91/1.10         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.91/1.10      inference('demod', [status(thm)], ['13', '14'])).
% 0.91/1.10  thf(t2_yellow19, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.91/1.10             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.91/1.10             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.91/1.10             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.91/1.10             ( m1_subset_1 @
% 0.91/1.10               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.91/1.10           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ X41)
% 0.91/1.10          | ~ (v1_subset_1 @ X41 @ (u1_struct_0 @ (k3_yellow_1 @ X42)))
% 0.91/1.10          | ~ (v2_waybel_0 @ X41 @ (k3_yellow_1 @ X42))
% 0.91/1.10          | ~ (v13_waybel_0 @ X41 @ (k3_yellow_1 @ X42))
% 0.91/1.10          | ~ (m1_subset_1 @ X41 @ 
% 0.91/1.10               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X42))))
% 0.91/1.10          | ~ (r2_hidden @ X43 @ X41)
% 0.91/1.10          | ~ (v1_xboole_0 @ X43)
% 0.91/1.10          | (v1_xboole_0 @ X42))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ X41)
% 0.91/1.10          | ~ (v1_subset_1 @ X41 @ 
% 0.91/1.10               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X42))))
% 0.91/1.10          | ~ (v2_waybel_0 @ X41 @ (k3_lattice3 @ (k1_lattice3 @ X42)))
% 0.91/1.10          | ~ (v13_waybel_0 @ X41 @ (k3_lattice3 @ (k1_lattice3 @ X42)))
% 0.91/1.10          | ~ (m1_subset_1 @ X41 @ 
% 0.91/1.10               (k1_zfmisc_1 @ 
% 0.91/1.10                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X42)))))
% 0.91/1.10          | ~ (r2_hidden @ X43 @ X41)
% 0.91/1.10          | ~ (v1_xboole_0 @ X43)
% 0.91/1.10          | (v1_xboole_0 @ X42))),
% 0.91/1.10      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.91/1.10          | ~ (v1_xboole_0 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.91/1.10          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.91/1.10               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.91/1.10          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.91/1.10               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.91/1.10          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.91/1.10               (u1_struct_0 @ 
% 0.91/1.10                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['15', '21'])).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      ((v13_waybel_0 @ sk_B_1 @ 
% 0.91/1.10        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.91/1.10      inference('demod', [status(thm)], ['23', '24'])).
% 0.91/1.10  thf('26', plain,
% 0.91/1.10      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      ((v2_waybel_0 @ sk_B_1 @ 
% 0.91/1.10        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.91/1.10      inference('demod', [status(thm)], ['26', '27'])).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      ((v1_subset_1 @ sk_B_1 @ 
% 0.91/1.10        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('31', plain,
% 0.91/1.10      ((v1_subset_1 @ sk_B_1 @ 
% 0.91/1.10        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.91/1.10      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.91/1.10          | ~ (v1_xboole_0 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['22', '25', '28', '31'])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | ~ (v1_xboole_0 @ (sk_C_1 @ sk_B_1 @ X0))
% 0.91/1.10          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['12', '32'])).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ X0)
% 0.91/1.10          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.91/1.10          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['11', '33'])).
% 0.91/1.10  thf('35', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.91/1.10          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.91/1.10          | ~ (v1_xboole_0 @ X0))),
% 0.91/1.10      inference('simplify', [status(thm)], ['34'])).
% 0.91/1.10  thf(fc5_struct_0, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.10       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.91/1.10  thf('36', plain,
% 0.91/1.10      (![X37 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ (k2_struct_0 @ X37))
% 0.91/1.10          | ~ (l1_struct_0 @ X37)
% 0.91/1.10          | (v2_struct_0 @ X37))),
% 0.91/1.10      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.91/1.10  thf('37', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ X0)
% 0.91/1.10          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | (v2_struct_0 @ sk_A)
% 0.91/1.10          | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.10  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('39', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ X0)
% 0.91/1.10          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | (v2_struct_0 @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['37', '38'])).
% 0.91/1.10  thf(t68_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.91/1.10       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.91/1.10            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.91/1.10  thf('40', plain,
% 0.91/1.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.91/1.10         (~ (r1_xboole_0 @ X25 @ X26)
% 0.91/1.10          | (v1_xboole_0 @ X27)
% 0.91/1.10          | ~ (r1_tarski @ X27 @ X25)
% 0.91/1.10          | ~ (r1_tarski @ X27 @ X26))),
% 0.91/1.10      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.91/1.10  thf('41', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((v2_struct_0 @ sk_A)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | ~ (v1_xboole_0 @ X0)
% 0.91/1.10          | ~ (r1_tarski @ X1 @ sk_B_1)
% 0.91/1.10          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.91/1.10          | (v1_xboole_0 @ X1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.10  thf('42', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ X0))
% 0.91/1.10          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B_1 @ X0) @ (k1_tarski @ X1))
% 0.91/1.10          | ~ (v1_xboole_0 @ X1)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | (v2_struct_0 @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['6', '41'])).
% 0.91/1.10  thf('43', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v2_struct_0 @ sk_A)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | ~ (v1_xboole_0 @ X0)
% 0.91/1.10          | (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['5', '42'])).
% 0.91/1.10  thf(d3_tarski, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( r1_tarski @ A @ B ) <=>
% 0.91/1.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.91/1.10  thf('44', plain,
% 0.91/1.10      (![X6 : $i, X8 : $i]:
% 0.91/1.10         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.91/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.10  thf(d1_xboole_0, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.10  thf('45', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.10  thf('46', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['44', '45'])).
% 0.91/1.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.91/1.10  thf('47', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.10  thf(d10_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.10  thf('48', plain,
% 0.91/1.10      (![X13 : $i, X15 : $i]:
% 0.91/1.10         (((X13) = (X15))
% 0.91/1.10          | ~ (r1_tarski @ X15 @ X13)
% 0.91/1.10          | ~ (r1_tarski @ X13 @ X15))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.10  thf('49', plain,
% 0.91/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.10  thf('50', plain,
% 0.91/1.10      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['46', '49'])).
% 0.91/1.10  thf(t4_boole, axiom,
% 0.91/1.10    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.10  thf('51', plain,
% 0.91/1.10      (![X24 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_boole])).
% 0.91/1.10  thf(t98_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.91/1.10  thf('52', plain,
% 0.91/1.10      (![X28 : $i, X29 : $i]:
% 0.91/1.10         ((k2_xboole_0 @ X28 @ X29)
% 0.91/1.10           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.91/1.10  thf('53', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['51', '52'])).
% 0.91/1.10  thf(t1_boole, axiom,
% 0.91/1.10    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.10  thf('54', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.10  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.10  thf('56', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['50', '55'])).
% 0.91/1.10  thf(t100_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.10  thf('57', plain,
% 0.91/1.10      (![X16 : $i, X17 : $i]:
% 0.91/1.10         ((k4_xboole_0 @ X16 @ X17)
% 0.91/1.10           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.10  thf('58', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 0.91/1.10          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['56', '57'])).
% 0.91/1.10  thf('59', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ X0)
% 0.91/1.10          | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10          | (v2_struct_0 @ sk_A)
% 0.91/1.10          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['43', '58'])).
% 0.91/1.10  thf('60', plain,
% 0.91/1.10      (((sk_B_1)
% 0.91/1.10         != (k2_yellow19 @ sk_A @ 
% 0.91/1.10             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('61', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ 
% 0.91/1.10        (k1_zfmisc_1 @ 
% 0.91/1.10         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.91/1.10      inference('demod', [status(thm)], ['13', '14'])).
% 0.91/1.10  thf(t14_yellow19, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.91/1.10             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.91/1.10             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.91/1.10             ( m1_subset_1 @
% 0.91/1.10               B @ 
% 0.91/1.10               ( k1_zfmisc_1 @
% 0.91/1.10                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.91/1.10           ( ( k7_subset_1 @
% 0.91/1.10               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.91/1.10               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.91/1.10             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.91/1.10  thf('62', plain,
% 0.91/1.10      (![X39 : $i, X40 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ X39)
% 0.91/1.10          | ~ (v2_waybel_0 @ X39 @ (k3_yellow_1 @ (k2_struct_0 @ X40)))
% 0.91/1.10          | ~ (v13_waybel_0 @ X39 @ (k3_yellow_1 @ (k2_struct_0 @ X40)))
% 0.91/1.10          | ~ (m1_subset_1 @ X39 @ 
% 0.91/1.10               (k1_zfmisc_1 @ 
% 0.91/1.10                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X40)))))
% 0.91/1.10          | ((k7_subset_1 @ 
% 0.91/1.10              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X40))) @ X39 @ 
% 0.91/1.10              (k1_tarski @ k1_xboole_0))
% 0.91/1.10              = (k2_yellow19 @ X40 @ 
% 0.91/1.10                 (k3_yellow19 @ X40 @ (k2_struct_0 @ X40) @ X39)))
% 0.91/1.10          | ~ (l1_struct_0 @ X40)
% 0.91/1.10          | (v2_struct_0 @ X40))),
% 0.91/1.10      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.91/1.10  thf('63', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('64', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('65', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('66', plain,
% 0.91/1.10      (![X38 : $i]: ((k3_yellow_1 @ X38) = (k3_lattice3 @ (k1_lattice3 @ X38)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.91/1.10  thf('67', plain,
% 0.91/1.10      (![X39 : $i, X40 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ X39)
% 0.91/1.10          | ~ (v2_waybel_0 @ X39 @ 
% 0.91/1.10               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X40))))
% 0.91/1.10          | ~ (v13_waybel_0 @ X39 @ 
% 0.91/1.10               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X40))))
% 0.91/1.10          | ~ (m1_subset_1 @ X39 @ 
% 0.91/1.10               (k1_zfmisc_1 @ 
% 0.91/1.10                (u1_struct_0 @ 
% 0.91/1.10                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X40))))))
% 0.91/1.10          | ((k7_subset_1 @ 
% 0.91/1.10              (u1_struct_0 @ 
% 0.91/1.10               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X40)))) @ 
% 0.91/1.10              X39 @ (k1_tarski @ k1_xboole_0))
% 0.91/1.10              = (k2_yellow19 @ X40 @ 
% 0.91/1.10                 (k3_yellow19 @ X40 @ (k2_struct_0 @ X40) @ X39)))
% 0.91/1.10          | ~ (l1_struct_0 @ X40)
% 0.91/1.10          | (v2_struct_0 @ X40))),
% 0.91/1.10      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.91/1.10  thf('68', plain,
% 0.91/1.10      (((v2_struct_0 @ sk_A)
% 0.91/1.10        | ~ (l1_struct_0 @ sk_A)
% 0.91/1.10        | ((k7_subset_1 @ 
% 0.91/1.10            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.91/1.10            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.91/1.10            = (k2_yellow19 @ sk_A @ 
% 0.91/1.10               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.91/1.10        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.91/1.10             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.91/1.10        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.91/1.10             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.91/1.10        | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['61', '67'])).
% 0.91/1.10  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('70', plain,
% 0.91/1.10      ((v13_waybel_0 @ sk_B_1 @ 
% 0.91/1.10        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.91/1.10      inference('demod', [status(thm)], ['23', '24'])).
% 0.91/1.10  thf('71', plain,
% 0.91/1.10      ((v2_waybel_0 @ sk_B_1 @ 
% 0.91/1.10        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.91/1.10      inference('demod', [status(thm)], ['26', '27'])).
% 0.91/1.10  thf('72', plain,
% 0.91/1.10      (((v2_struct_0 @ sk_A)
% 0.91/1.10        | ((k7_subset_1 @ 
% 0.91/1.10            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.91/1.10            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.91/1.10            = (k2_yellow19 @ sk_A @ 
% 0.91/1.10               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.91/1.10        | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.91/1.10  thf('73', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ 
% 0.91/1.10        (k1_zfmisc_1 @ 
% 0.91/1.10         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.91/1.10      inference('demod', [status(thm)], ['13', '14'])).
% 0.91/1.10  thf(redefinition_k7_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.10       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.91/1.10  thf('74', plain,
% 0.91/1.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.91/1.10          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.91/1.10  thf('75', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k7_subset_1 @ 
% 0.91/1.10           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.91/1.10           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['73', '74'])).
% 0.91/1.10  thf('76', plain,
% 0.91/1.10      (((v2_struct_0 @ sk_A)
% 0.91/1.10        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.91/1.10            = (k2_yellow19 @ sk_A @ 
% 0.91/1.10               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.91/1.10        | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['72', '75'])).
% 0.91/1.10  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('78', plain,
% 0.91/1.10      (((v1_xboole_0 @ sk_B_1)
% 0.91/1.10        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.91/1.10            = (k2_yellow19 @ sk_A @ 
% 0.91/1.10               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.91/1.10      inference('clc', [status(thm)], ['76', '77'])).
% 0.91/1.10  thf('79', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('80', plain,
% 0.91/1.10      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.91/1.10         = (k2_yellow19 @ sk_A @ 
% 0.91/1.10            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.91/1.10      inference('clc', [status(thm)], ['78', '79'])).
% 0.91/1.10  thf('81', plain,
% 0.91/1.10      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.91/1.10      inference('demod', [status(thm)], ['60', '80'])).
% 0.91/1.10  thf('82', plain,
% 0.91/1.10      ((((sk_B_1) != (sk_B_1))
% 0.91/1.10        | (v2_struct_0 @ sk_A)
% 0.91/1.10        | (v1_xboole_0 @ sk_B_1)
% 0.91/1.10        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['59', '81'])).
% 0.91/1.10  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.10  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.10  thf('84', plain,
% 0.91/1.10      ((((sk_B_1) != (sk_B_1)) | (v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['82', '83'])).
% 0.91/1.10  thf('85', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.91/1.10      inference('simplify', [status(thm)], ['84'])).
% 0.91/1.10  thf('86', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('87', plain, ((v2_struct_0 @ sk_A)),
% 0.91/1.10      inference('clc', [status(thm)], ['85', '86'])).
% 0.91/1.10  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
