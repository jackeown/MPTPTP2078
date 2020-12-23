%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tMUGeESa16

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:37 EST 2020

% Result     : Theorem 6.63s
% Output     : Refutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 619 expanded)
%              Number of leaves         :   38 ( 183 expanded)
%              Depth                    :   30
%              Number of atoms          : 1893 (10121 expanded)
%              Number of equality atoms :    5 (  13 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t34_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_connsp_2 @ D @ A @ C )
                   => ~ ( r1_xboole_0 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
                <=> ! [D: $i] :
                      ( ( m1_connsp_2 @ D @ A @ C )
                     => ~ ( r1_xboole_0 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d13_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( r1_xboole_0 @ B @ E )
                              & ( r2_hidden @ D @ E )
                              & ( v3_pre_topc @ E @ A ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( v3_pre_topc @ E @ A )
        & ( r2_hidden @ D @ E )
        & ( r1_xboole_0 @ B @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k2_pre_topc @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X9 @ X5 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X9 @ X5 @ X6 )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k2_pre_topc @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r2_hidden @ X9 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X40: $i] :
      ( ~ ( m1_connsp_2 @ X40 @ sk_A @ sk_C )
      | ~ ( r1_xboole_0 @ X40 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ! [X40: $i] :
        ( ~ ( m1_connsp_2 @ X40 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X40 @ sk_B ) )
   <= ! [X40: $i] :
        ( ~ ( m1_connsp_2 @ X40 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X40 @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('53',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('54',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('55',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_connsp_2 @ X21 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_connsp_2 @ X13 @ X12 @ X11 )
      | ( r2_hidden @ X11 @ ( k1_tops_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
        | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
        | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( r2_hidden @ sk_C @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('77',plain,
    ( ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ sk_A )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
   <= ( r1_xboole_0 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('83',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ sk_D_1 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ sk_D_1 )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('87',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ~ ( r1_xboole_0 @ X38 @ X39 )
      | ( r1_xboole_0 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ X0 )
        | ~ ( r1_xboole_0 @ sk_D_1 @ X0 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ sk_B )
   <= ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('91',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X3 @ X0 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_pre_topc @ X0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('93',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
        | ( zip_tseitin_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ X1 @ sk_B @ X0 ) )
   <= ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) )
   <= ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','93'])).

thf('95',plain,
    ( ( zip_tseitin_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ sk_C @ sk_B @ sk_A )
   <= ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('98',plain,
    ( ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('102',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X5 @ X6 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ X1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( zip_tseitin_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ X0 @ sk_B @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','108'])).

thf('110',plain,
    ( ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','110'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('112',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('115',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_D_1 @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_D_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ! [X40: $i] :
        ( ~ ( m1_connsp_2 @ X40 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X40 @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('121',plain,(
    ! [X40: $i] :
      ( ~ ( m1_connsp_2 @ X40 @ sk_A @ sk_C )
      | ~ ( r1_xboole_0 @ X40 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['49','51','119','120'])).

thf('122',plain,(
    ! [X40: $i] :
      ( ~ ( m1_connsp_2 @ X40 @ sk_A @ sk_C )
      | ~ ( r1_xboole_0 @ X40 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['47','121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_xboole_0 @ ( sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','122'])).

thf('124',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('129',plain,(
    ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['49','51','119'])).

thf('130',plain,(
    ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['128','129'])).

thf('131',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('135',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['0','135'])).


%------------------------------------------------------------------------------
