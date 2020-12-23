%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5XNzc6xBSt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 382 expanded)
%              Number of leaves         :   18 ( 109 expanded)
%              Depth                    :   28
%              Number of atoms          :  699 (7554 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t24_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) )
                      | ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) )
                        | ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( m1_pre_topc @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_pre_topc @ C @ A )
                & ~ ( v2_struct_0 @ C ) )
             => ! [D: $i] :
                  ( ( ( m1_pre_topc @ D @ A )
                    & ~ ( v2_struct_0 @ D ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ D @ C )
                        & ~ ( r1_tsep_1 @ C @ D ) )
                      | ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_1 @ D @ B )
     => ( ( r1_tsep_1 @ B @ D )
        & ( r1_tsep_1 @ D @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_0 @ D @ C )
     => ( ~ ( r1_tsep_1 @ C @ D )
        & ~ ( r1_tsep_1 @ D @ C ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( zip_tseitin_1 @ D @ B )
                      | ( zip_tseitin_0 @ D @ C ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( zip_tseitin_0 @ X6 @ X7 )
      | ( zip_tseitin_1 @ X6 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X5 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ sk_B )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ sk_B )
      | ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_D @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tsep_1 @ X3 @ X2 )
      | ~ ( zip_tseitin_1 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_D @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tsep_1 @ X2 @ X3 )
      | ~ ( zip_tseitin_1 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('25',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( zip_tseitin_0 @ sk_D @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('36',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('49',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('50',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['34','47','48','49'])).

thf('51',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['16','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','51'])).

thf('56',plain,
    ( ~ ( zip_tseitin_0 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['65','48'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['54','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5XNzc6xBSt
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 62 iterations in 0.031s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.49  thf(t24_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.49                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.49                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t23_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 0.21/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                     ( ( ( ~( r1_tsep_1 @ D @ C ) ) & 
% 0.21/0.49                         ( ~( r1_tsep_1 @ C @ D ) ) ) | 
% 0.21/0.49                       ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_2, axiom,
% 0.21/0.49    (![D:$i,B:$i]:
% 0.21/0.49     ( ( zip_tseitin_1 @ D @ B ) =>
% 0.21/0.49       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ))).
% 0.21/0.49  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_4, axiom,
% 0.21/0.49    (![D:$i,C:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ D @ C ) =>
% 0.21/0.49       ( ( ~( r1_tsep_1 @ C @ D ) ) & ( ~( r1_tsep_1 @ D @ C ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_5, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                     ( ( zip_tseitin_1 @ D @ B ) | ( zip_tseitin_0 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X4)
% 0.21/0.49          | ~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.49          | (v2_struct_0 @ X6)
% 0.21/0.49          | ~ (m1_pre_topc @ X6 @ X5)
% 0.21/0.49          | (zip_tseitin_0 @ X6 @ X7)
% 0.21/0.49          | (zip_tseitin_1 @ X6 @ X4)
% 0.21/0.49          | ~ (m1_pre_topc @ X4 @ X7)
% 0.21/0.49          | ~ (m1_pre_topc @ X7 @ X5)
% 0.21/0.49          | (v2_struct_0 @ X7)
% 0.21/0.49          | ~ (l1_pre_topc @ X5)
% 0.21/0.49          | ~ (v2_pre_topc @ X5)
% 0.21/0.49          | (v2_struct_0 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.49          | (zip_tseitin_1 @ X1 @ sk_B)
% 0.21/0.49          | (zip_tseitin_0 @ X1 @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.49          | (zip_tseitin_1 @ X1 @ sk_B)
% 0.21/0.49          | (zip_tseitin_0 @ X1 @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ X1)
% 0.21/0.49          | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | (zip_tseitin_0 @ X0 @ sk_C)
% 0.21/0.49          | (zip_tseitin_1 @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_B @ sk_C)
% 0.21/0.49          | (v2_struct_0 @ sk_C)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | (zip_tseitin_0 @ X0 @ sk_C)
% 0.21/0.49          | (zip_tseitin_1 @ X0 @ sk_B)
% 0.21/0.49          | (v2_struct_0 @ sk_C)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (zip_tseitin_1 @ sk_D @ sk_B)
% 0.21/0.49        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tsep_1 @ X3 @ X2) | ~ (zip_tseitin_1 @ X3 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (zip_tseitin_1 @ sk_D @ sk_B)
% 0.21/0.49        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '11'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tsep_1 @ X2 @ X3) | ~ (zip_tseitin_1 @ X3 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['15'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_B))) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tsep_1 @ X1 @ X0) | ~ (zip_tseitin_0 @ X1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B)
% 0.21/0.49         | (v2_struct_0 @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.49  thf('27', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_C))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_B))) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tsep_1 @ X0 @ X1) | ~ (zip_tseitin_0 @ X1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B)
% 0.21/0.49         | (v2_struct_0 @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.49  thf('40', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_C))
% 0.21/0.49         <= (~ ((r1_tsep_1 @ sk_B @ sk_D)) & ((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain, (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.49      inference('split', [status(esa)], ['22'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.49      inference('split', [status(esa)], ['15'])).
% 0.21/0.49  thf('50', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['34', '47', '48', '49'])).
% 0.21/0.49  thf('51', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['16', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B)
% 0.21/0.49         | (v2_struct_0 @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '51'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((~ (zip_tseitin_0 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B)
% 0.21/0.49         | (v2_struct_0 @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain, (((v2_struct_0 @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, (~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.49  thf('66', plain, (((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['65', '48'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['54', '66'])).
% 0.21/0.49  thf('68', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('71', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.21/0.49      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.49  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('73', plain, ((v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('clc', [status(thm)], ['71', '72'])).
% 0.21/0.49  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
