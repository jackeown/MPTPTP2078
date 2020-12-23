%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1147+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1zDHB8vxej

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:09 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  187 (3292 expanded)
%              Number of leaves         :   39 ( 936 expanded)
%              Depth                    :   32
%              Number of atoms          : 1749 (49442 expanded)
%              Number of equality atoms :   23 (  96 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t39_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v3_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ? [D: $i] :
                    ( ( v6_orders_2 @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                    & ( r2_hidden @ B @ D )
                    & ( r2_hidden @ C @ D ) )
              <=> ( ( r2_orders_2 @ A @ B @ C )
                <=> ~ ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
    <=> ( ( r2_orders_2 @ A @ B @ C )
      <=> ~ ( r1_orders_2 @ A @ C @ B ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_4 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ D )
        & ( r2_hidden @ B @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v6_orders_2 @ D @ A ) ) ) )).

thf(zf_stmt_4,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ? [D: $i] :
                    ( zip_tseitin_4 @ D @ C @ B @ A )
              <=> ( zip_tseitin_5 @ C @ B @ A ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ? [D: $i] :
                      ( zip_tseitin_4 @ D @ C @ B @ A )
                <=> ( zip_tseitin_5 @ C @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_4])).

thf('0',plain,(
    ! [X31: $i] :
      ( ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1',plain,
    ( ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
    | ! [X31: $i] :
        ~ ( zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_orders_2 @ X27 @ X28 @ X29 )
      | ( r2_orders_2 @ X27 @ X29 @ X28 )
      | ~ ( zip_tseitin_5 @ X28 @ X29 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t38_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v3_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( ! [D: $i] :
                        ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                          & ( v6_orders_2 @ D @ A ) )
                       => ~ ( ( r2_hidden @ C @ D )
                            & ( r2_hidden @ B @ D ) ) )
                    & ( ( r1_orders_2 @ A @ C @ B )
                      | ( r1_orders_2 @ A @ B @ C ) ) )
                & ~ ( ~ ( r1_orders_2 @ A @ C @ B )
                    & ~ ( r1_orders_2 @ A @ B @ C )
                    & ? [D: $i] :
                        ( ( v6_orders_2 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ B @ D )
                        & ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( r1_orders_2 @ A @ B @ C )
        | ( r1_orders_2 @ A @ C @ B ) )
     => ( zip_tseitin_3 @ C @ B @ A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_3 @ X15 @ X16 @ X17 )
      | ~ ( r1_orders_2 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('8',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( zip_tseitin_3 @ sk_C @ sk_B @ sk_A ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

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

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( zip_tseitin_3 @ sk_C @ sk_B @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_3 @ X15 @ X16 @ X17 )
      | ~ ( r1_orders_2 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('18',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ A )
       => ~ ( zip_tseitin_1 @ D @ C @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(zf_stmt_8,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B )
     => ( ( r2_hidden @ B @ D )
        & ( r2_hidden @ C @ D ) ) ) )).

thf(zf_stmt_12,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [D: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ A )
     => ( ( v6_orders_2 @ D @ A )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_14,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( ? [D: $i] :
                        ( ( r2_hidden @ C @ D )
                        & ( r2_hidden @ B @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( v6_orders_2 @ D @ A ) )
                    & ~ ( r1_orders_2 @ A @ B @ C )
                    & ~ ( r1_orders_2 @ A @ C @ B ) )
                & ~ ( ( zip_tseitin_3 @ C @ B @ A )
                    & ! [D: $i] :
                        ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X20 @ X18 @ X19 ) @ X20 @ X18 @ X19 )
      | ~ ( zip_tseitin_3 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('34',plain,
    ( ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ( zip_tseitin_4 @ X23 @ X22 @ X24 @ X26 )
      | ~ ( v6_orders_2 @ X23 @ X26 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v6_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ( zip_tseitin_4 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 @ X1 @ sk_A ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v6_orders_2 @ X6 @ X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('48',plain,
    ( ( v6_orders_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( zip_tseitin_4 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 @ X1 @ sk_A ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_4 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,
    ( ( zip_tseitin_4 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf('52',plain,
    ( ! [X31: $i] :
        ~ ( zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A )
   <= ! [X31: $i] :
        ~ ( zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ~ ! [X31: $i] :
          ~ ( zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','53'])).

thf('55',plain,(
    ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( zip_tseitin_4 @ X23 @ X22 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X20 @ X18 )
      | ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v6_orders_2 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v6_orders_2 @ sk_D_1 @ sk_A )
        | ~ ( r2_hidden @ X1 @ sk_D_1 )
        | ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ( r1_orders_2 @ sk_A @ X1 @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,
    ( ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v6_orders_2 @ X23 @ X25 )
      | ~ ( zip_tseitin_4 @ X23 @ X22 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,
    ( ( v6_orders_2 @ sk_D_1 @ sk_A )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ sk_D_1 )
        | ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ( r1_orders_2 @ sk_A @ X1 @ X0 )
        | ( r1_orders_2 @ sk_A @ X0 @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64','67'])).

thf('69',plain,
    ( ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('70',plain,(
    zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','53','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['57','71'])).

thf('73',plain,
    ( ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_4 @ X23 @ X22 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('75',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','53','69'])).

thf('77',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_D_1 )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','78'])).

thf('80',plain,
    ( ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( zip_tseitin_4 @ X23 @ X22 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('82',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','53','69'])).

thf('84',plain,(
    r2_hidden @ sk_C @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_C = sk_B )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B = sk_C )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ( sk_C = sk_B )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( sk_C = sk_B ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( sk_C = sk_B )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_5 @ X28 @ X29 @ X30 )
      | ~ ( r1_orders_2 @ X30 @ X28 @ X29 )
      | ( r2_orders_2 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('112',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_C = sk_B )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
    | ( sk_C = sk_B )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('115',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_C = sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_5 @ X28 @ X29 @ X30 )
      | ( r1_orders_2 @ X30 @ X28 @ X29 )
      | ~ ( r2_orders_2 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,
    ( ( sk_C = sk_B )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_B )
    | ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( sk_C = sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t30_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r1_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('121',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_orders_2 @ X4 @ X5 @ X3 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t30_orders_2])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,
    ( ( sk_C = sk_B )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['118','126'])).

thf('128',plain,
    ( ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('129',plain,(
    ~ ( zip_tseitin_5 @ sk_C @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('130',plain,(
    sk_C = sk_B ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('133',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('135',plain,
    ( ( r1_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_5 @ X28 @ X29 @ X30 )
      | ~ ( r1_orders_2 @ X30 @ X28 @ X29 )
      | ( r2_orders_2 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ( zip_tseitin_5 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('141',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','141'])).

thf('143',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('144',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    zip_tseitin_5 @ sk_B @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['138','144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['55','130','145'])).


%------------------------------------------------------------------------------
