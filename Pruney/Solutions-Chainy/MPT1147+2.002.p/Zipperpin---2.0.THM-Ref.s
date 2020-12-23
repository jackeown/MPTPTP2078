%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONJ8SbTk5b

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONJ8SbTk5b
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 233 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.20/0.54  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.54  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(t39_orders_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( ?[D:$i]:
% 0.20/0.54                   ( ( v6_orders_2 @ D @ A ) & 
% 0.20/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.54                     ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) <=>
% 0.20/0.54                 ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.20/0.54                   ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_5 @ C @ B @ A ) <=>
% 0.20/0.54       ( ( r2_orders_2 @ A @ B @ C ) <=> ( ~( r1_orders_2 @ A @ C @ B ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_4 @ D @ C @ B @ A ) <=>
% 0.20/0.54       ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.20/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.54         ( v6_orders_2 @ D @ A ) ) ))).
% 0.20/0.54  thf(zf_stmt_4, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( ?[D:$i]: ( zip_tseitin_4 @ D @ C @ B @ A ) ) <=>
% 0.20/0.54                 ( zip_tseitin_5 @ C @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_5, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                  ( ( ?[D:$i]: ( zip_tseitin_4 @ D @ C @ B @ A ) ) <=>
% 0.20/0.54                    ( zip_tseitin_5 @ C @ B @ A ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [zf_stmt_4])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X31 : $i]:
% 0.20/0.54         (~ (zip_tseitin_5 @ sk_C @ sk_B @ sk_A)
% 0.20/0.54          | ~ (zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((~ (zip_tseitin_5 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (~ ((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (~ ((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)) | 
% 0.20/0.54       (![X31 : $i]: ~ (zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)
% 0.20/0.54        | (zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.54         ((r1_orders_2 @ X27 @ X28 @ X29)
% 0.20/0.54          | (r2_orders_2 @ X27 @ X29 @ X28)
% 0.20/0.54          | ~ (zip_tseitin_5 @ X28 @ X29 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54         | (r1_orders_2 @ sk_A @ sk_C @ sk_B)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf(t38_orders_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( ~( ( ![D:$i]:
% 0.20/0.54                        ( ( ( m1_subset_1 @
% 0.20/0.54                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.54                            ( v6_orders_2 @ D @ A ) ) =>
% 0.20/0.54                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.54                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 0.20/0.54                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 0.20/0.54                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 0.20/0.54                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.20/0.54                      ( ?[D:$i]:
% 0.20/0.54                        ( ( v6_orders_2 @ D @ A ) & 
% 0.20/0.54                          ( m1_subset_1 @
% 0.20/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.54                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_6, axiom,
% 0.20/0.54    (![C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.20/0.54       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_3 @ X15 @ X16 @ X17) | ~ (r1_orders_2 @ X17 @ X15 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54         | (zip_tseitin_3 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf(d10_orders_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_orders_2 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.20/0.54                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (l1_orders_2 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_orders_2 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | ~ (r2_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((((zip_tseitin_3 @ sk_C @ sk_B @ sk_A)
% 0.20/0.54         | (r1_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_3 @ X15 @ X16 @ X17) | ~ (r1_orders_2 @ X17 @ X16 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((zip_tseitin_3 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf(zf_stmt_7, axiom,
% 0.20/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 0.20/0.54       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.54         ((zip_tseitin_2 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.54          | (zip_tseitin_1 @ X11 @ X12 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.54  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf(zf_stmt_8, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_10, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_11, axiom,
% 0.20/0.54    (![D:$i,C:$i,B:$i]:
% 0.20/0.54     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 0.20/0.54       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 0.20/0.54  thf(zf_stmt_12, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_13, axiom,
% 0.20/0.54    (![D:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ D @ A ) =>
% 0.20/0.54       ( ( v6_orders_2 @ D @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_14, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ( ~( ( ?[D:$i]:
% 0.20/0.54                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.20/0.54                          ( m1_subset_1 @
% 0.20/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.54                          ( v6_orders_2 @ D @ A ) ) ) & 
% 0.20/0.54                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.20/0.54                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 0.20/0.54                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 0.20/0.54                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.54          | ~ (zip_tseitin_2 @ (sk_D @ X20 @ X18 @ X19) @ X20 @ X18 @ X19)
% 0.20/0.54          | ~ (zip_tseitin_3 @ X20 @ X18 @ X19)
% 0.20/0.54          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.20/0.54          | ~ (l1_orders_2 @ X19)
% 0.20/0.54          | ~ (v3_orders_2 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v3_orders_2 @ sk_A)
% 0.20/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.20/0.54          | ~ (zip_tseitin_2 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.20/0.54          | ~ (zip_tseitin_2 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((zip_tseitin_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 0.20/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.54         | (zip_tseitin_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '26'])).
% 0.20/0.54  thf('28', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (((zip_tseitin_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((r2_hidden @ X8 @ X9) | ~ (zip_tseitin_1 @ X9 @ X10 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_11])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (((zip_tseitin_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((r2_hidden @ X10 @ X9) | ~ (zip_tseitin_1 @ X9 @ X10 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_11])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (((r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (((zip_tseitin_3 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.54         ((zip_tseitin_2 @ X11 @ X12 @ X13 @ X14) | (zip_tseitin_0 @ X11 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.20/0.54          | ~ (zip_tseitin_2 @ (sk_D @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.54         | (zip_tseitin_0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.54  thf('40', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((zip_tseitin_0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.54          | ~ (zip_tseitin_0 @ X6 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.20/0.54         ((zip_tseitin_4 @ X23 @ X22 @ X24 @ X26)
% 0.20/0.54          | ~ (v6_orders_2 @ X23 @ X26)
% 0.20/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.54          | ~ (r2_hidden @ X24 @ X23)
% 0.20/0.54          | ~ (r2_hidden @ X22 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          (~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.54           | ~ (r2_hidden @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.54           | ~ (v6_orders_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.54           | (zip_tseitin_4 @ (sk_D @ sk_C @ sk_B @ sk_A) @ X0 @ X1 @ sk_A)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (((zip_tseitin_0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         ((v6_orders_2 @ X6 @ X7) | ~ (zip_tseitin_0 @ X6 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((v6_orders_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          (~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.54           | ~ (r2_hidden @ X1 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.54           | (zip_tseitin_4 @ (sk_D @ sk_C @ sk_B @ sk_A) @ X0 @ X1 @ sk_A)))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['45', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          ((zip_tseitin_4 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C @ X0 @ sk_A)
% 0.20/0.54           | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (((zip_tseitin_4 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((![X31 : $i]: ~ (zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= ((![X31 : $i]: ~ (zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (~ (![X31 : $i]: ~ (zip_tseitin_4 @ X31 @ sk_C @ sk_B @ sk_A)) | 
% 0.20/0.54       ~ ((zip_tseitin_5 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain, (~ ((zip_tseitin_5 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53'])).
% 0.20/0.54  thf('55', plain, (~ (zip_tseitin_5 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.20/0.54  thf('56', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.54          | ~ (zip_tseitin_4 @ X23 @ X22 @ X24 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.20/0.54          | (r1_orders_2 @ X19 @ X20 @ X18)
% 0.20/0.54          | (r1_orders_2 @ X19 @ X18 @ X20)
% 0.20/0.54          | ~ (r2_hidden @ X20 @ X21)
% 0.20/0.54          | ~ (r2_hidden @ X18 @ X21)
% 0.20/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.54          | ~ (v6_orders_2 @ X21 @ X19)
% 0.20/0.54          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.20/0.54          | ~ (l1_orders_2 @ X19)
% 0.20/0.54          | ~ (v3_orders_2 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          (~ (v3_orders_2 @ sk_A)
% 0.20/0.54           | ~ (l1_orders_2 @ sk_A)
% 0.20/0.54           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54           | ~ (v6_orders_2 @ sk_D_1 @ sk_A)
% 0.20/0.54           | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.20/0.54           | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.54           | (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.54           | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.54           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.54         ((v6_orders_2 @ X23 @ X25) | ~ (zip_tseitin_4 @ X23 @ X22 @ X24 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (((v6_orders_2 @ sk_D_1 @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54           | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.20/0.54           | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.54           | (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.54           | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.54           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['62', '63', '64', '67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) | 
% 0.20/0.54       ((zip_tseitin_5 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('70', plain, (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53', '69'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (r2_hidden @ X1 @ sk_D_1)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.54          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.54          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.54          | ~ (r2_hidden @ sk_B @ sk_D_1)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '71'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.54         ((r2_hidden @ X24 @ X23) | ~ (zip_tseitin_4 @ X23 @ X22 @ X24 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_D_1))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.54  thf('76', plain, (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53', '69'])).
% 0.20/0.54  thf('77', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['72', '77'])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_C @ sk_D_1)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '78'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['3'])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.54         ((r2_hidden @ X22 @ X23) | ~ (zip_tseitin_4 @ X23 @ X22 @ X24 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (((r2_hidden @ sk_C @ sk_D_1))
% 0.20/0.54         <= (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain, (((zip_tseitin_4 @ sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53', '69'])).
% 0.20/0.54  thf('84', plain, ((r2_hidden @ sk_C @ sk_D_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      (((r1_orders_2 @ sk_A @ sk_C @ sk_B) | (r1_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['79', '84'])).
% 0.20/0.54  thf('86', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('87', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ((X0) = (X2))
% 0.20/0.54          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (l1_orders_2 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_orders_2 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.54          | ((sk_C) = (X0))
% 0.20/0.54          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.54  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r2_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.54          | ((sk_C) = (X0))
% 0.20/0.54          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['86', '91'])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['85', '92'])).
% 0.20/0.54  thf('94', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ((X0) = (X2))
% 0.20/0.54          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (l1_orders_2 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_orders_2 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | ((sk_B) = (X0))
% 0.20/0.54          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.54  thf('98', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | ((sk_B) = (X0))
% 0.20/0.54          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | ((sk_B) = (sk_C))
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['94', '99'])).
% 0.20/0.54  thf('101', plain,
% 0.20/0.54      ((((sk_C) = (sk_B))
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | ((sk_B) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '100'])).
% 0.20/0.54  thf('102', plain,
% 0.20/0.54      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['101'])).
% 0.20/0.54  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('104', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (l1_orders_2 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.54  thf('106', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_orders_2 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.54          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.54  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('108', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.54          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['106', '107'])).
% 0.20/0.54  thf('109', plain,
% 0.20/0.54      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['103', '108'])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      ((((sk_C) = (sk_B))
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['102', '109'])).
% 0.20/0.54  thf('111', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.54         ((zip_tseitin_5 @ X28 @ X29 @ X30)
% 0.20/0.54          | ~ (r1_orders_2 @ X30 @ X28 @ X29)
% 0.20/0.54          | (r2_orders_2 @ X30 @ X29 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('112', plain,
% 0.20/0.54      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | (zip_tseitin_5 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A)
% 0.20/0.54        | ((sk_C) = (sk_B))
% 0.20/0.54        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['112'])).
% 0.20/0.54  thf('114', plain, (~ (zip_tseitin_5 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.20/0.54  thf('115', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['113', '114'])).
% 0.20/0.54  thf('116', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.54         ((zip_tseitin_5 @ X28 @ X29 @ X30)
% 0.20/0.54          | (r1_orders_2 @ X30 @ X28 @ X29)
% 0.20/0.54          | ~ (r2_orders_2 @ X30 @ X29 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('117', plain,
% 0.20/0.54      ((((sk_C) = (sk_B))
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (zip_tseitin_5 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.54  thf('118', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C) | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['113', '114'])).
% 0.20/0.54  thf('119', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('120', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf(t30_orders_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54               ( ~( ( r1_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('121', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (r2_orders_2 @ X4 @ X5 @ X3)
% 0.20/0.54          | ~ (r1_orders_2 @ X4 @ X3 @ X5)
% 0.20/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (l1_orders_2 @ X4)
% 0.20/0.54          | ~ (v5_orders_2 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t30_orders_2])).
% 0.20/0.54  thf('122', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v5_orders_2 @ sk_A)
% 0.20/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.54          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['120', '121'])).
% 0.20/0.54  thf('123', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('125', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.20/0.54          | ~ (r2_orders_2 @ sk_A @ X0 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.20/0.54  thf('126', plain,
% 0.20/0.54      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54        | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['119', '125'])).
% 0.20/0.54  thf('127', plain,
% 0.20/0.54      ((((sk_C) = (sk_B)) | ~ (r1_orders_2 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['118', '126'])).
% 0.20/0.54  thf('128', plain,
% 0.20/0.54      (((zip_tseitin_5 @ sk_C @ sk_B @ sk_A) | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['117', '127'])).
% 0.20/0.54  thf('129', plain, (~ (zip_tseitin_5 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.20/0.54  thf('130', plain, (((sk_C) = (sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['128', '129'])).
% 0.20/0.54  thf('131', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('132', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54          | (r1_orders_2 @ sk_A @ sk_B @ X0)
% 0.20/0.54          | (r1_orders_2 @ sk_A @ X0 @ sk_B)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['72', '77'])).
% 0.20/0.54  thf('133', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_B @ sk_D_1)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.54  thf('134', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.20/0.54  thf('135', plain,
% 0.20/0.54      (((r1_orders_2 @ sk_A @ sk_B @ sk_B) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['133', '134'])).
% 0.20/0.54  thf('136', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.54      inference('simplify', [status(thm)], ['135'])).
% 0.20/0.54  thf('137', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.54         ((zip_tseitin_5 @ X28 @ X29 @ X30)
% 0.20/0.54          | ~ (r1_orders_2 @ X30 @ X28 @ X29)
% 0.20/0.54          | (r2_orders_2 @ X30 @ X29 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('138', plain,
% 0.20/0.54      (((r2_orders_2 @ sk_A @ sk_B @ sk_B)
% 0.20/0.54        | (zip_tseitin_5 @ sk_B @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['136', '137'])).
% 0.20/0.54  thf('139', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('140', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.54          | ((X0) != (X2))
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.54          | ~ (l1_orders_2 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.20/0.54  thf('141', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (l1_orders_2 @ X1)
% 0.20/0.54          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.20/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['140'])).
% 0.20/0.54  thf('142', plain,
% 0.20/0.54      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_B) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['139', '141'])).
% 0.20/0.54  thf('143', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('144', plain, (~ (r2_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['142', '143'])).
% 0.20/0.54  thf('145', plain, ((zip_tseitin_5 @ sk_B @ sk_B @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['138', '144'])).
% 0.20/0.54  thf('146', plain, ($false),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '130', '145'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
