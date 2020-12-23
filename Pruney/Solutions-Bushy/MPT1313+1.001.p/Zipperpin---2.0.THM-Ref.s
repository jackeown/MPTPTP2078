%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1313+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cFZwlllfUv

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 332 expanded)
%              Number of leaves         :   24 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          : 1068 (5330 expanded)
%              Number of equality atoms :   25 ( 146 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t32_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v3_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
               => ( ( v3_pre_topc @ C @ B )
                <=> ? [D: $i] :
                      ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                        = C )
                      & ( v3_pre_topc @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_tops_2])).

thf('0',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X14 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
       != sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X14: $i] :
        ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X14 @ sk_A )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
         != sk_C_1 ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
      = sk_C_1 )
    | ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_B )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X7 ) )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X9 @ X7 @ X8 ) @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ X0 ) @ sk_C_1 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ X0 ) @ sk_C_1 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ X0 ) @ sk_C_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X4
        = ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,
    ( ( sk_C_1
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X14: $i] :
        ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X14 @ sk_A )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
         != sk_C_1 ) )
   <= ! [X14: $i] :
        ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X14 @ sk_A )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
         != sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ~ ( v3_pre_topc @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X14: $i] :
          ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X14 @ sk_A )
          | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
           != sk_C_1 ) )
      & ( v3_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('39',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( u1_pre_topc @ X5 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ! [X14: $i] :
          ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X14 @ sk_A )
          | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
           != sk_C_1 ) )
      & ( v3_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','41','42'])).

thf('44',plain,
    ( ~ ! [X14: $i] :
          ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X14 @ sk_A )
          | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X14 @ ( k2_struct_0 @ sk_B ) )
           != sk_C_1 ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
      = sk_C_1 )
    | ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
      = sk_C_1 )
   <= ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
      = sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('50',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ sk_D_2 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( r2_hidden @ sk_D_2 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_D_2 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X2 @ X6 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X6 ) )
      | ( X4
       != ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,(
    ! [X2: $i,X3: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X6 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( zip_tseitin_0 @ X3 @ ( k9_subset_1 @ ( u1_struct_0 @ X2 ) @ X3 @ ( k2_struct_0 @ X2 ) ) @ X2 @ X6 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_D_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_D_2 @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A )
        | ~ ( r2_hidden @ sk_D_2 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_D_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_D_2 @ ( k2_struct_0 @ X0 ) ) @ X0 @ sk_A )
   <= ( ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,
    ( ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
   <= ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
        = sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['46','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X7 @ X8 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ sk_C_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ sk_C_1 @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
        = sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) )
   <= ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
        = sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v3_pre_topc @ sk_C_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_B )
   <= ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
        = sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ sk_C_1 @ sk_B )
   <= ~ ( v3_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('76',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k2_struct_0 @ sk_B ) )
     != sk_C_1 )
    | ( v3_pre_topc @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','44','45','76'])).


%------------------------------------------------------------------------------
