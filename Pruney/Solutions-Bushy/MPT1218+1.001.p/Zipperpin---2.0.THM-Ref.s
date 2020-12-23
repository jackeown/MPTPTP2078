%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1218+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TFU3h5HWeN

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:16 EST 2020

% Result     : Theorem 8.76s
% Output     : Refutation 8.76s
% Verified   : 
% Statistics : Number of formulae       :  257 (2590 expanded)
%              Number of leaves         :   44 ( 786 expanded)
%              Depth                    :   36
%              Number of atoms          : 2597 (32521 expanded)
%              Number of equality atoms :   32 (1021 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v18_lattices_type,type,(
    v18_lattices: $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k4_lattices_type,type,(
    k4_lattices: $i > $i > $i > $i )).

thf(v19_lattices_type,type,(
    v19_lattices: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( sk_B @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t54_lattices,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v18_lattices @ B @ A )
            & ( v19_lattices @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( B
            = ( k2_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v18_lattices @ B @ A )
              & ( v19_lattices @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( B
              = ( k2_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_lattices])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(t23_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( r1_lattices @ A @ ( k4_lattices @ A @ B @ C ) @ B ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r1_lattices @ X24 @ ( k4_lattices @ X24 @ X23 @ X25 ) @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v8_lattices @ X24 )
      | ~ ( v6_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','18','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( sk_B @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( sk_B @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k4_lattices @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ~ ( v6_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( k4_lattices @ X15 @ X14 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_lattices])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('35',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('36',plain,(
    ! [X18: $i] :
      ( ( l1_lattices @ X18 )
      | ~ ( l3_lattices @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('37',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v9_lattices @ X21 )
      | ~ ( v8_lattices @ X21 )
      | ~ ( v6_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r3_lattices @ X21 @ X20 @ X22 )
      | ~ ( r1_lattices @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('45',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( sk_B @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d22_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v18_lattices @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r3_lattices @ A @ C @ D )
                        & ( r2_hidden @ D @ B ) )
                     => ( r2_hidden @ C @ B ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v18_lattices @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r3_lattices @ X5 @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d22_lattices])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v18_lattices @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v18_lattices @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['73','74'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf(dt_l1_lattices,axiom,(
    ! [A: $i] :
      ( ( l1_lattices @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('80',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_lattices @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_lattices])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('86',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('89',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( X37 = X35 )
      | ( m1_subset_1 @ ( sk_D_2 @ X35 @ X37 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('93',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_B_1
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('98',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('102',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('103',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r1_lattices @ X24 @ ( k4_lattices @ X24 @ X23 @ X25 ) @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v8_lattices @ X24 )
      | ~ ( v6_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_lattices])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('106',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('107',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','110'])).

thf('112',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('113',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(commutativity_k4_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( l1_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k4_lattices @ A @ B @ C )
        = ( k4_lattices @ A @ C @ B ) ) ) )).

thf('114',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ~ ( v6_lattices @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( ( k4_lattices @ X2 @ X1 @ X3 )
        = ( k4_lattices @ X2 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_lattices])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('117',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['112','120'])).

thf('122',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['112','120'])).

thf('124',plain,
    ( ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
      = ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('126',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 )
        = ( k4_lattices @ sk_A @ X0 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('133',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','133'])).

thf('135',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['121','134'])).

thf('136',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','135'])).

thf('137',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('139',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l3_lattices @ X21 )
      | ~ ( v9_lattices @ X21 )
      | ~ ( v8_lattices @ X21 )
      | ~ ( v6_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r3_lattices @ X21 @ X20 @ X22 )
      | ~ ( r1_lattices @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('143',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('144',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('145',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','133'])).

thf('148',plain,
    ( ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','133'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','149'])).

thf('151',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('157',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d23_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v19_lattices @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r3_lattices @ A @ C @ D )
                        & ( r2_hidden @ C @ B ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('159',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v19_lattices @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r3_lattices @ X9 @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v10_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d23_lattices])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v19_lattices @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v19_lattices @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','164'])).

thf('166',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ X0 ) @ ( sk_B @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('168',plain,(
    r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ sk_B_1 ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','177'])).

thf('179',plain,(
    r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( sk_B @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('180',plain,(
    m1_subset_1 @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['73','74'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','184'])).

thf('186',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('187',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['178','189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    r2_hidden @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r3_lattices @ sk_A @ ( k4_lattices @ sk_A @ ( sk_B @ sk_B_1 ) @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['165','193'])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','194'])).

thf('196',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    r2_hidden @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( X37 = X35 )
      | ~ ( r2_hidden @ ( sk_D_2 @ X35 @ X37 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ ( sk_D_2 @ X35 @ X37 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['199','202'])).

thf('204',plain,(
    sk_B_1
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ~ ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','205'])).

thf('207',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('209',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','209'])).

thf('211',plain,(
    $false ),
    inference('sup-',[status(thm)],['75','210'])).


%------------------------------------------------------------------------------
