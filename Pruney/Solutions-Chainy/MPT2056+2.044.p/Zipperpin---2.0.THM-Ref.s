%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hGzlzc83eg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:46 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 228 expanded)
%              Number of leaves         :   44 (  92 expanded)
%              Depth                    :   24
%              Number of atoms          : 1205 (2666 expanded)
%              Number of equality atoms :   59 ( 119 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

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

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) )
      | ( X23 = X24 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_yellow_1 @ X33 ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_yellow_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('22',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','30','33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_C @ X0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','55'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('69',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','73'])).

thf('75',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) @ X30 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('78',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('79',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) ) @ X30 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('89',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','94'])).

thf('96',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','95'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,
    ( ( sk_B != sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hGzlzc83eg
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:29:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 253 iterations in 0.133s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.59  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.59  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.59  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.59  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.59  thf(t15_yellow19, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.59             ( v1_subset_1 @
% 0.40/0.59               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.59             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.59             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.59             ( m1_subset_1 @
% 0.40/0.59               B @ 
% 0.40/0.59               ( k1_zfmisc_1 @
% 0.40/0.59                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.59           ( ( B ) =
% 0.40/0.59             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.59                ( v1_subset_1 @
% 0.40/0.59                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.59                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.59                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.59                ( m1_subset_1 @
% 0.40/0.59                  B @ 
% 0.40/0.59                  ( k1_zfmisc_1 @
% 0.40/0.59                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.59              ( ( B ) =
% 0.40/0.59                ( k2_yellow19 @
% 0.40/0.59                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.40/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d5_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.40/0.59       ( ![D:$i]:
% 0.40/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.40/0.59         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.40/0.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.40/0.59          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.40/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.59  thf('2', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.59  thf(l24_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.59  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.40/0.59          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.59  thf(t4_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_boole])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.40/0.59          | ((X1) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf(t3_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.59  thf(t17_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( A ) != ( B ) ) =>
% 0.40/0.59       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X23 : $i, X24 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24))
% 0.40/0.59          | ((X23) = (X24)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.40/0.59          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d2_yellow_1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf(t2_yellow19, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.59             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.40/0.59             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.40/0.59             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.40/0.59             ( m1_subset_1 @
% 0.40/0.59               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.40/0.59           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X32)
% 0.40/0.59          | ~ (v1_subset_1 @ X32 @ (u1_struct_0 @ (k3_yellow_1 @ X33)))
% 0.40/0.59          | ~ (v2_waybel_0 @ X32 @ (k3_yellow_1 @ X33))
% 0.40/0.59          | ~ (v13_waybel_0 @ X32 @ (k3_yellow_1 @ X33))
% 0.40/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.40/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X33))))
% 0.40/0.59          | ~ (r2_hidden @ X34 @ X32)
% 0.40/0.59          | ~ (v1_xboole_0 @ X34)
% 0.40/0.59          | (v1_xboole_0 @ X33))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X32)
% 0.40/0.59          | ~ (v1_subset_1 @ X32 @ 
% 0.40/0.59               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X33))))
% 0.40/0.59          | ~ (v2_waybel_0 @ X32 @ (k3_lattice3 @ (k1_lattice3 @ X33)))
% 0.40/0.59          | ~ (v13_waybel_0 @ X32 @ (k3_lattice3 @ (k1_lattice3 @ X33)))
% 0.40/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X33)))))
% 0.40/0.59          | ~ (r2_hidden @ X34 @ X32)
% 0.40/0.59          | ~ (v1_xboole_0 @ X34)
% 0.40/0.59          | (v1_xboole_0 @ X33))),
% 0.40/0.59      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.59          | ~ (v1_xboole_0 @ X0)
% 0.40/0.59          | ~ (r2_hidden @ X0 @ sk_B)
% 0.40/0.59          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.59          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.59          | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.59               (u1_struct_0 @ 
% 0.40/0.59                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.59          | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.59        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.59        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((v1_subset_1 @ sk_B @ 
% 0.40/0.59        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      ((v1_subset_1 @ sk_B @ 
% 0.40/0.59        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.59          | ~ (v1_xboole_0 @ X0)
% 0.40/0.59          | ~ (r2_hidden @ X0 @ sk_B)
% 0.40/0.59          | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['27', '30', '33', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X0 @ sk_B)
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | ~ (v1_xboole_0 @ (sk_C @ sk_B @ X0))
% 0.40/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '37'])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ X0)
% 0.40/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.40/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['16', '38'])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.40/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.40/0.59  thf(fc5_struct_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X28 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (k2_struct_0 @ X28))
% 0.40/0.59          | ~ (l1_struct_0 @ X28)
% 0.40/0.59          | (v2_struct_0 @ X28))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ X0)
% 0.40/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ X0)
% 0.40/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B)
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ sk_A)
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | ~ (v1_xboole_0 @ X0)
% 0.40/0.59          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ sk_B @ X0)
% 0.40/0.59          | ~ (v1_xboole_0 @ (sk_C @ X0 @ sk_B))
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['13', '46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ X0)
% 0.40/0.59          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '47'])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.40/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.59  thf(t4_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.40/0.59          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.59          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ X0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (v1_xboole_0 @ X0)
% 0.40/0.59          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ X0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_xboole_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '55'])).
% 0.40/0.59  thf(t100_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X14 @ X15)
% 0.40/0.59           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.40/0.59            = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.40/0.59          | ((X1) = (k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf(t3_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('60', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf(t48_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      (![X17 : $i, X18 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.40/0.59           = (k3_xboole_0 @ X17 @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.40/0.59          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.40/0.59          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.40/0.59  thf('65', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['64', '65'])).
% 0.40/0.59  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['59', '66'])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X14 @ X15)
% 0.40/0.59           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.59  thf('70', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.40/0.59           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('73', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['67', '72'])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B))
% 0.40/0.59          | (v1_xboole_0 @ sk_B)
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['58', '73'])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (((sk_B)
% 0.40/0.59         != (k2_yellow19 @ sk_A @ 
% 0.40/0.59             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf(t14_yellow19, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.59             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.59             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.59             ( m1_subset_1 @
% 0.40/0.59               B @ 
% 0.40/0.59               ( k1_zfmisc_1 @
% 0.40/0.59                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.59           ( ( k7_subset_1 @
% 0.40/0.59               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.40/0.59               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.40/0.59             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X30)
% 0.40/0.59          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 0.40/0.59          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 0.40/0.59          | ~ (m1_subset_1 @ X30 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))))
% 0.40/0.59          | ((k7_subset_1 @ 
% 0.40/0.59              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31))) @ X30 @ 
% 0.40/0.59              (k1_tarski @ k1_xboole_0))
% 0.40/0.59              = (k2_yellow19 @ X31 @ 
% 0.40/0.59                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 0.40/0.59          | ~ (l1_struct_0 @ X31)
% 0.40/0.59          | (v2_struct_0 @ X31))),
% 0.40/0.59      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('81', plain,
% 0.40/0.59      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i]:
% 0.40/0.59         ((v1_xboole_0 @ X30)
% 0.40/0.59          | ~ (v2_waybel_0 @ X30 @ 
% 0.40/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 0.40/0.59          | ~ (v13_waybel_0 @ X30 @ 
% 0.40/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 0.40/0.59          | ~ (m1_subset_1 @ X30 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (u1_struct_0 @ 
% 0.40/0.59                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))))
% 0.40/0.59          | ((k7_subset_1 @ 
% 0.40/0.59              (u1_struct_0 @ 
% 0.40/0.59               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31)))) @ 
% 0.40/0.59              X30 @ (k1_tarski @ k1_xboole_0))
% 0.40/0.59              = (k2_yellow19 @ X31 @ 
% 0.40/0.59                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 0.40/0.59          | ~ (l1_struct_0 @ X31)
% 0.40/0.59          | (v2_struct_0 @ X31))),
% 0.40/0.59      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.40/0.59  thf('83', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.59        | ((k7_subset_1 @ 
% 0.40/0.59            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.40/0.59            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.40/0.59            = (k2_yellow19 @ sk_A @ 
% 0.40/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.59        | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.59             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.59        | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.59             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.59        | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['76', '82'])).
% 0.40/0.59  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_B @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf(redefinition_k7_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.59  thf('86', plain,
% 0.40/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.40/0.59          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k7_subset_1 @ 
% 0.40/0.59           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.40/0.59           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['85', '86'])).
% 0.40/0.59  thf('88', plain,
% 0.40/0.59      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.59        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.59        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('90', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.40/0.59            = (k2_yellow19 @ sk_A @ 
% 0.40/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.59        | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['83', '84', '87', '88', '89'])).
% 0.40/0.59  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('92', plain,
% 0.40/0.59      (((v1_xboole_0 @ sk_B)
% 0.40/0.59        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.40/0.59            = (k2_yellow19 @ sk_A @ 
% 0.40/0.59               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.59      inference('clc', [status(thm)], ['90', '91'])).
% 0.40/0.59  thf('93', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.40/0.59         = (k2_yellow19 @ sk_A @ 
% 0.40/0.59            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.59      inference('clc', [status(thm)], ['92', '93'])).
% 0.40/0.59  thf('95', plain,
% 0.40/0.59      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['75', '94'])).
% 0.40/0.59  thf('96', plain,
% 0.40/0.59      ((((sk_B) != (sk_B))
% 0.40/0.59        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['74', '95'])).
% 0.40/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.59  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.59  thf('98', plain,
% 0.40/0.59      ((((sk_B) != (sk_B)) | (v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['96', '97'])).
% 0.40/0.59  thf('99', plain, (((v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('simplify', [status(thm)], ['98'])).
% 0.40/0.59  thf('100', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('101', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('clc', [status(thm)], ['99', '100'])).
% 0.40/0.59  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
