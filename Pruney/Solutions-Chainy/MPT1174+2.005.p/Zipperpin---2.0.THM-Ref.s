%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o9PBt8F7Ut

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:09 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 540 expanded)
%              Number of leaves         :   34 ( 173 expanded)
%              Depth                    :   27
%              Number of atoms          : 1458 (11188 expanded)
%              Number of equality atoms :   24 ( 514 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t81_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ C )
                 => ( ( B
                      = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) )
                   => ( ( k3_orders_2 @ A @ D @ B )
                      = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ C )
                   => ( ( B
                        = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) )
                     => ( ( k3_orders_2 @ A @ D @ B )
                        = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_orders_2 @ X5 @ X4 @ X6 )
      | ( X4 != X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( r2_orders_2 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_orders_1 @ sk_C @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m2_orders_2 @ X12 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k3_orders_2 @ X21 @ X22 @ X23 ) )
      | ( r2_orders_2 @ X21 @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_orders_2 @ sk_A @ sk_D @ X0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_B_1 )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_B_1 )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( ( r2_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ C @ D ) )
                      | ( ( r1_orders_2 @ A @ B @ C )
                        & ( r2_orders_2 @ A @ C @ D ) ) )
                   => ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r2_orders_2 @ X17 @ X16 @ X18 )
      | ~ ( r2_orders_2 @ X17 @ X19 @ X18 )
      | ~ ( r1_orders_2 @ X17 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t32_orders_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_orders_2 @ sk_A @ sk_B_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r2_hidden @ X20 @ ( k3_orders_2 @ X21 @ X22 @ X23 ) )
      | ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_D )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k3_orders_2 @ sk_A @ sk_D @ X0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_D )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_D )
    | ( ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ sk_D ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('80',plain,
    ( sk_B_1
    = ( k1_funct_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_orders_1 @ D @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m2_orders_2 @ E @ A @ D )
                     => ( ( ( r2_hidden @ B @ E )
                          & ( C
                            = ( k1_funct_1 @ D @ ( u1_struct_0 @ A ) ) ) )
                       => ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_orders_1 @ X26 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( X27
       != ( k1_funct_1 @ X26 @ ( u1_struct_0 @ X25 ) ) )
      | ( r3_orders_2 @ X25 @ X27 @ X24 )
      | ~ ( r2_hidden @ X24 @ X28 )
      | ~ ( m2_orders_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_orders_2])).

thf('82',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X26 @ ( u1_struct_0 @ X25 ) ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m2_orders_2 @ X28 @ X25 @ X26 )
      | ~ ( r2_hidden @ X24 @ X28 )
      | ( r3_orders_2 @ X25 @ ( k1_funct_1 @ X26 @ ( u1_struct_0 @ X25 ) ) @ X24 )
      | ~ ( m1_orders_1 @ X26 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_orders_1 @ sk_C @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r3_orders_2 @ sk_A @ ( k1_funct_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_C )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_orders_1 @ sk_C @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( sk_B_1
    = ( k1_funct_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_C )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ X0 )
      | ( r3_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf('93',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) )
    | ~ ( m2_orders_2 @ sk_D @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,(
    m2_orders_2 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r3_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r3_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('99',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( r3_orders_2 @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    r1_orders_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_B @ ( k3_orders_2 @ sk_A @ sk_D @ sk_B_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['60','108'])).

thf('110',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['5','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o9PBt8F7Ut
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 307 iterations in 0.315s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.58/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.77  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.77  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.58/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.77  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.58/0.77  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.77  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.77  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.58/0.77  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.58/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.77  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.77  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.58/0.77  thf(t81_orders_2, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.58/0.77                   ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77                     ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.77          ( ![B:$i]:
% 0.58/0.77            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77              ( ![C:$i]:
% 0.58/0.77                ( ( m1_orders_1 @ C @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77                  ( ![D:$i]:
% 0.58/0.77                    ( ( m2_orders_2 @ D @ A @ C ) =>
% 0.58/0.77                      ( ( ( B ) = ( k1_funct_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77                        ( ( k3_orders_2 @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t81_orders_2])).
% 0.58/0.77  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d10_orders_2, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_orders_2 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.58/0.77                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.58/0.77          | ~ (r2_orders_2 @ X5 @ X4 @ X6)
% 0.58/0.77          | ((X4) != (X6))
% 0.58/0.77          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.58/0.77          | ~ (l1_orders_2 @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X5 : $i, X6 : $i]:
% 0.58/0.77         (~ (l1_orders_2 @ X5)
% 0.58/0.77          | ~ (r2_orders_2 @ X5 @ X6 @ X6)
% 0.58/0.77          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['1'])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      ((~ (r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1) | ~ (l1_orders_2 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '2'])).
% 0.58/0.77  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('5', plain, (~ (r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.77  thf(t7_xboole_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.77          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('8', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      ((m1_orders_1 @ sk_C @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(dt_m2_orders_2, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.58/0.77         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.77       ( ![C:$i]:
% 0.58/0.77         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.58/0.77           ( ( v6_orders_2 @ C @ A ) & 
% 0.58/0.77             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.77         (~ (l1_orders_2 @ X10)
% 0.58/0.77          | ~ (v5_orders_2 @ X10)
% 0.58/0.77          | ~ (v4_orders_2 @ X10)
% 0.58/0.77          | ~ (v3_orders_2 @ X10)
% 0.58/0.77          | (v2_struct_0 @ X10)
% 0.58/0.77          | ~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X10)))
% 0.58/0.77          | (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.58/0.77          | ~ (m2_orders_2 @ X12 @ X10 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C)
% 0.58/0.77          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.77  thf('12', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('13', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m2_orders_2 @ X0 @ sk_A @ sk_C)
% 0.58/0.77          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.58/0.77  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.58/0.77      inference('clc', [status(thm)], ['16', '17'])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['8', '18'])).
% 0.58/0.77  thf(dt_k3_orders_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.58/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77       ( m1_subset_1 @
% 0.58/0.77         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.58/0.77          | ~ (l1_orders_2 @ X8)
% 0.58/0.77          | ~ (v5_orders_2 @ X8)
% 0.58/0.77          | ~ (v4_orders_2 @ X8)
% 0.58/0.77          | ~ (v3_orders_2 @ X8)
% 0.58/0.77          | (v2_struct_0 @ X8)
% 0.58/0.77          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.58/0.77          | (m1_subset_1 @ (k3_orders_2 @ X8 @ X7 @ X9) @ 
% 0.58/0.77             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.58/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.77  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.58/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.58/0.77  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ X0) @ 
% 0.58/0.77             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.77      inference('clc', [status(thm)], ['26', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1) @ 
% 0.58/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['7', '28'])).
% 0.58/0.77  thf(t4_subset, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.58/0.77       ( m1_subset_1 @ A @ C ) ))).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X1 @ X2)
% 0.58/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.58/0.77          | (m1_subset_1 @ X1 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      ((((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) = (k1_xboole_0))
% 0.58/0.77        | (m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77           (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['6', '31'])).
% 0.58/0.77  thf('33', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) != (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77        (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['8', '18'])).
% 0.58/0.77  thf(t57_orders_2, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.58/0.77                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.58/0.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.58/0.77          | ~ (r2_hidden @ X20 @ (k3_orders_2 @ X21 @ X22 @ X23))
% 0.58/0.77          | (r2_orders_2 @ X21 @ X20 @ X23)
% 0.58/0.77          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.58/0.77          | ~ (l1_orders_2 @ X21)
% 0.58/0.77          | ~ (v5_orders_2 @ X21)
% 0.58/0.77          | ~ (v4_orders_2 @ X21)
% 0.58/0.77          | ~ (v3_orders_2 @ X21)
% 0.58/0.77          | (v2_struct_0 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.58/0.77          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.58/0.77          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k3_orders_2 @ sk_A @ sk_D @ X0) = (k1_xboole_0))
% 0.58/0.77          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 0.58/0.77               (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_orders_2 @ sk_A @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 0.58/0.77             X0)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['35', '43'])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.77        | (r2_orders_2 @ sk_A @ 
% 0.58/0.77           (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_B_1)
% 0.58/0.77        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['34', '44'])).
% 0.58/0.77  thf('46', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | (r2_orders_2 @ sk_A @ 
% 0.58/0.77           (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_B_1)
% 0.58/0.77        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['45', '46'])).
% 0.58/0.77  thf('48', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) != (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | (r2_orders_2 @ sk_A @ 
% 0.58/0.77           (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_B_1))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.58/0.77  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      ((r2_orders_2 @ sk_A @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77        sk_B_1)),
% 0.58/0.77      inference('clc', [status(thm)], ['49', '50'])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77        (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('53', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t32_orders_2, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77                   ( ( ( ( r2_orders_2 @ A @ B @ C ) & 
% 0.58/0.77                         ( r1_orders_2 @ A @ C @ D ) ) | 
% 0.58/0.77                       ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.58/0.77                         ( r2_orders_2 @ A @ C @ D ) ) ) =>
% 0.58/0.77                     ( r2_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.58/0.77          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.58/0.77          | (r2_orders_2 @ X17 @ X16 @ X18)
% 0.58/0.77          | ~ (r2_orders_2 @ X17 @ X19 @ X18)
% 0.58/0.77          | ~ (r1_orders_2 @ X17 @ X16 @ X19)
% 0.58/0.77          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.58/0.77          | ~ (l1_orders_2 @ X17)
% 0.58/0.77          | ~ (v5_orders_2 @ X17)
% 0.58/0.77          | ~ (v4_orders_2 @ X17))),
% 0.58/0.77      inference('cnf', [status(esa)], [t32_orders_2])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v4_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.58/0.77          | (r2_orders_2 @ sk_A @ sk_B_1 @ X1)
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.77  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('59', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (r2_orders_2 @ sk_A @ X0 @ X1)
% 0.58/0.77          | (r2_orders_2 @ sk_A @ sk_B_1 @ X1)
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (r2_orders_2 @ sk_A @ 
% 0.58/0.77               (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ X0)
% 0.58/0.77          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77               (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['52', '59'])).
% 0.58/0.77  thf('61', plain,
% 0.58/0.77      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77        (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('62', plain,
% 0.58/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('63', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['8', '18'])).
% 0.58/0.77  thf('64', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.58/0.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.58/0.77          | ~ (r2_hidden @ X20 @ (k3_orders_2 @ X21 @ X22 @ X23))
% 0.58/0.77          | (r2_hidden @ X20 @ X22)
% 0.58/0.77          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.58/0.77          | ~ (l1_orders_2 @ X21)
% 0.58/0.77          | ~ (v5_orders_2 @ X21)
% 0.58/0.77          | ~ (v4_orders_2 @ X21)
% 0.58/0.77          | ~ (v3_orders_2 @ X21)
% 0.58/0.77          | (v2_struct_0 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_hidden @ X1 @ sk_D)
% 0.58/0.77          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.77  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_hidden @ X1 @ sk_D)
% 0.58/0.77          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_D @ X0))
% 0.58/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.58/0.77  thf('71', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k3_orders_2 @ sk_A @ sk_D @ X0) = (k1_xboole_0))
% 0.58/0.77          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ 
% 0.58/0.77               (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ X0)) @ sk_D)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['62', '70'])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.77        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_D)
% 0.58/0.77        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['61', '71'])).
% 0.58/0.77  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('74', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_D)
% 0.58/0.77        | ((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['72', '73'])).
% 0.58/0.77  thf('75', plain, (((k3_orders_2 @ sk_A @ sk_D @ sk_B_1) != (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('76', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_D))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('78', plain,
% 0.58/0.77      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ sk_D)),
% 0.58/0.77      inference('clc', [status(thm)], ['76', '77'])).
% 0.58/0.77  thf('79', plain,
% 0.58/0.77      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77        (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('80', plain, (((sk_B_1) = (k1_funct_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t80_orders_2, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.77               ( ![D:$i]:
% 0.58/0.77                 ( ( m1_orders_1 @ D @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77                   ( ![E:$i]:
% 0.58/0.77                     ( ( m2_orders_2 @ E @ A @ D ) =>
% 0.58/0.77                       ( ( ( r2_hidden @ B @ E ) & 
% 0.58/0.77                           ( ( C ) = ( k1_funct_1 @ D @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.77                         ( r3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('81', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.58/0.77          | ~ (m1_orders_1 @ X26 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 0.58/0.77          | ((X27) != (k1_funct_1 @ X26 @ (u1_struct_0 @ X25)))
% 0.58/0.77          | (r3_orders_2 @ X25 @ X27 @ X24)
% 0.58/0.77          | ~ (r2_hidden @ X24 @ X28)
% 0.58/0.77          | ~ (m2_orders_2 @ X28 @ X25 @ X26)
% 0.58/0.77          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.58/0.77          | ~ (l1_orders_2 @ X25)
% 0.58/0.77          | ~ (v5_orders_2 @ X25)
% 0.58/0.77          | ~ (v4_orders_2 @ X25)
% 0.58/0.77          | ~ (v3_orders_2 @ X25)
% 0.58/0.77          | (v2_struct_0 @ X25))),
% 0.58/0.77      inference('cnf', [status(esa)], [t80_orders_2])).
% 0.58/0.77  thf('82', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.58/0.77         ((v2_struct_0 @ X25)
% 0.58/0.77          | ~ (v3_orders_2 @ X25)
% 0.58/0.77          | ~ (v4_orders_2 @ X25)
% 0.58/0.77          | ~ (v5_orders_2 @ X25)
% 0.58/0.77          | ~ (l1_orders_2 @ X25)
% 0.58/0.77          | ~ (m1_subset_1 @ (k1_funct_1 @ X26 @ (u1_struct_0 @ X25)) @ 
% 0.58/0.77               (u1_struct_0 @ X25))
% 0.58/0.77          | ~ (m2_orders_2 @ X28 @ X25 @ X26)
% 0.58/0.77          | ~ (r2_hidden @ X24 @ X28)
% 0.58/0.77          | (r3_orders_2 @ X25 @ (k1_funct_1 @ X26 @ (u1_struct_0 @ X25)) @ X24)
% 0.58/0.77          | ~ (m1_orders_1 @ X26 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 0.58/0.77          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['81'])).
% 0.58/0.77  thf('83', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | ~ (m1_orders_1 @ sk_C @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77          | (r3_orders_2 @ sk_A @ (k1_funct_1 @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.58/0.77             X0)
% 0.58/0.77          | ~ (r2_hidden @ X0 @ X1)
% 0.58/0.77          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['80', '82'])).
% 0.58/0.77  thf('84', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('85', plain,
% 0.58/0.77      ((m1_orders_1 @ sk_C @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('86', plain, (((sk_B_1) = (k1_funct_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('89', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('90', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('91', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r3_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (r2_hidden @ X0 @ X1)
% 0.58/0.77          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_C)
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['83', '84', '85', '86', '87', '88', '89', '90'])).
% 0.58/0.77  thf('92', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_C)
% 0.58/0.77          | ~ (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ X0)
% 0.58/0.77          | (r3_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77             (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['79', '91'])).
% 0.58/0.77  thf('93', plain,
% 0.58/0.77      (((r3_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77         (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)))
% 0.58/0.77        | ~ (m2_orders_2 @ sk_D @ sk_A @ sk_C)
% 0.58/0.77        | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['78', '92'])).
% 0.58/0.77  thf('94', plain, ((m2_orders_2 @ sk_D @ sk_A @ sk_C)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('95', plain,
% 0.58/0.77      (((r3_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77         (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)))
% 0.58/0.77        | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['93', '94'])).
% 0.58/0.77  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('97', plain,
% 0.58/0.77      ((r3_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77        (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)))),
% 0.58/0.77      inference('clc', [status(thm)], ['95', '96'])).
% 0.58/0.77  thf('98', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(redefinition_r3_orders_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.77         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.58/0.77  thf('99', plain,
% 0.58/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.58/0.77          | ~ (l1_orders_2 @ X14)
% 0.58/0.77          | ~ (v3_orders_2 @ X14)
% 0.58/0.77          | (v2_struct_0 @ X14)
% 0.58/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.77          | (r1_orders_2 @ X14 @ X13 @ X15)
% 0.58/0.77          | ~ (r3_orders_2 @ X14 @ X13 @ X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.58/0.77  thf('100', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r3_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | (r1_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (v2_struct_0 @ sk_A)
% 0.58/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['98', '99'])).
% 0.58/0.77  thf('101', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('103', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r3_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | (r1_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (v2_struct_0 @ sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.58/0.77  thf('104', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77             (u1_struct_0 @ sk_A))
% 0.58/0.77        | (r1_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77           (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['97', '103'])).
% 0.58/0.77  thf('105', plain,
% 0.58/0.77      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ 
% 0.58/0.77        (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('106', plain,
% 0.58/0.77      (((v2_struct_0 @ sk_A)
% 0.58/0.77        | (r1_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77           (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1))))),
% 0.58/0.77      inference('demod', [status(thm)], ['104', '105'])).
% 0.58/0.77  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('108', plain,
% 0.58/0.77      ((r1_orders_2 @ sk_A @ sk_B_1 @ 
% 0.58/0.77        (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)))),
% 0.58/0.77      inference('clc', [status(thm)], ['106', '107'])).
% 0.58/0.77  thf('109', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.77          | (r2_orders_2 @ sk_A @ sk_B_1 @ X0)
% 0.58/0.77          | ~ (r2_orders_2 @ sk_A @ 
% 0.58/0.77               (sk_B @ (k3_orders_2 @ sk_A @ sk_D @ sk_B_1)) @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['60', '108'])).
% 0.58/0.77  thf('110', plain,
% 0.58/0.77      (((r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)
% 0.58/0.77        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['51', '109'])).
% 0.58/0.77  thf('111', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('112', plain, ((r2_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['110', '111'])).
% 0.58/0.77  thf('113', plain, ($false), inference('demod', [status(thm)], ['5', '112'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
