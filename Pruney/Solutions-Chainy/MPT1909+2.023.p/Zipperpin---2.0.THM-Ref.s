%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7RJlJBnfS

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 514 expanded)
%              Number of leaves         :   43 ( 166 expanded)
%              Depth                    :   24
%              Number of atoms          : 1308 (15574 expanded)
%              Number of equality atoms :   39 ( 433 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t77_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                            = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_borsuk_1 @ C @ A @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( D = E )
                           => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                              = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_pre_topc @ X49 @ X50 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_xboole_0 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v3_tex_2 @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 )
      | ( v2_struct_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_pre_topc @ X51 @ X52 )
      | ~ ( v4_tex_2 @ X51 @ X52 )
      | ( X53
       != ( u1_struct_0 @ X51 ) )
      | ( v3_tex_2 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('14',plain,(
    ! [X51: $i,X52: $i] :
      ( ( v2_struct_0 @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X51 ) @ X52 )
      | ~ ( v4_tex_2 @ X51 @ X52 )
      | ~ ( m1_pre_topc @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( ( k6_domain_1 @ X44 @ X45 )
        = ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ X44 )
      | ( ( k6_domain_1 @ X44 @ X45 )
        = ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X42 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X42 @ X41 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ X47 )
      | ( ( k7_domain_1 @ X47 @ X46 @ X48 )
        = ( k2_tarski @ X46 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ X0 )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ X0 )
        = ( k2_tarski @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D )
    = ( k2_tarski @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('58',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('62',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                            = ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( v2_struct_0 @ X56 )
      | ~ ( v4_tex_2 @ X56 @ X57 )
      | ~ ( m1_pre_topc @ X56 @ X57 )
      | ~ ( v3_borsuk_1 @ X58 @ X57 @ X56 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( X59 != X60 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) @ X58 @ X59 )
        = ( k2_pre_topc @ X57 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) ) ) )
      | ~ ( v5_pre_topc @ X58 @ X57 @ X56 )
      | ~ ( v1_funct_2 @ X58 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v3_tdlat_3 @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('67',plain,(
    ! [X56: $i,X57: $i,X58: $i,X60: $i] :
      ( ( v2_struct_0 @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ~ ( v3_tdlat_3 @ X57 )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) )
      | ~ ( v5_pre_topc @ X58 @ X57 @ X56 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) ) ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X57 ) @ ( u1_struct_0 @ X56 ) @ X58 @ X60 )
        = ( k2_pre_topc @ X57 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v3_borsuk_1 @ X58 @ X57 @ X56 )
      | ~ ( m1_pre_topc @ X56 @ X57 )
      | ~ ( v4_tex_2 @ X56 @ X57 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74','75','76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('88',plain,(
    m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D @ sk_D )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('90',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('98',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','98'])).

thf('100',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['22','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7RJlJBnfS
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.92  % Solved by: fo/fo7.sh
% 0.72/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.92  % done 731 iterations in 0.464s
% 0.72/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.92  % SZS output start Refutation
% 0.72/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.72/0.92  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.72/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.72/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.72/0.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.72/0.92  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.72/0.92  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.72/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.72/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.92  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.72/0.92  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.72/0.92  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.72/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.92  thf(k7_domain_1_type, type, k7_domain_1: $i > $i > $i > $i).
% 0.72/0.92  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.72/0.92  thf(sk_B_type, type, sk_B: $i > $i).
% 0.72/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.92  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.72/0.92  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.72/0.92  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.72/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.92  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.72/0.92  thf(sk_E_type, type, sk_E: $i).
% 0.72/0.92  thf(t77_tex_2, conjecture,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.72/0.92         ( l1_pre_topc @ A ) ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.72/0.92             ( m1_pre_topc @ B @ A ) ) =>
% 0.72/0.92           ( ![C:$i]:
% 0.72/0.92             ( ( ( v1_funct_1 @ C ) & 
% 0.72/0.92                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.72/0.92                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.72/0.92                 ( m1_subset_1 @
% 0.72/0.92                   C @ 
% 0.72/0.92                   ( k1_zfmisc_1 @
% 0.72/0.92                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.72/0.92               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.72/0.92                 ( ![D:$i]:
% 0.72/0.92                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.72/0.92                     ( ![E:$i]:
% 0.72/0.92                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.72/0.92                         ( ( ( D ) = ( E ) ) =>
% 0.72/0.92                           ( ( k8_relset_1 @
% 0.72/0.92                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.72/0.92                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.72/0.92                             ( k2_pre_topc @
% 0.72/0.92                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.72/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.92    (~( ![A:$i]:
% 0.72/0.92        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.72/0.92            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.72/0.92          ( ![B:$i]:
% 0.72/0.92            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.72/0.92                ( m1_pre_topc @ B @ A ) ) =>
% 0.72/0.92              ( ![C:$i]:
% 0.72/0.92                ( ( ( v1_funct_1 @ C ) & 
% 0.72/0.92                    ( v1_funct_2 @
% 0.72/0.92                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.72/0.92                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.72/0.92                    ( m1_subset_1 @
% 0.72/0.92                      C @ 
% 0.72/0.92                      ( k1_zfmisc_1 @
% 0.72/0.92                        ( k2_zfmisc_1 @
% 0.72/0.92                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.72/0.92                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.72/0.92                    ( ![D:$i]:
% 0.72/0.92                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.72/0.92                        ( ![E:$i]:
% 0.72/0.92                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.72/0.92                            ( ( ( D ) = ( E ) ) =>
% 0.72/0.92                              ( ( k8_relset_1 @
% 0.72/0.92                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.72/0.92                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.72/0.92                                ( k2_pre_topc @
% 0.72/0.92                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.72/0.92    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.72/0.92  thf('0', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(t1_tsep_1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( l1_pre_topc @ A ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( m1_pre_topc @ B @ A ) =>
% 0.72/0.92           ( m1_subset_1 @
% 0.72/0.92             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.72/0.92  thf('1', plain,
% 0.72/0.92      (![X49 : $i, X50 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X49 @ X50)
% 0.72/0.92          | (m1_subset_1 @ (u1_struct_0 @ X49) @ 
% 0.72/0.92             (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.72/0.92          | ~ (l1_pre_topc @ X50))),
% 0.72/0.92      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.72/0.92  thf('2', plain,
% 0.72/0.92      ((~ (l1_pre_topc @ sk_A)
% 0.72/0.92        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['0', '1'])).
% 0.72/0.92  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('4', plain,
% 0.72/0.92      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.72/0.92  thf(t46_tex_2, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( ( v1_xboole_0 @ B ) & 
% 0.72/0.92             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.72/0.92           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.72/0.92  thf('5', plain,
% 0.72/0.92      (![X54 : $i, X55 : $i]:
% 0.72/0.92         (~ (v1_xboole_0 @ X54)
% 0.72/0.92          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.72/0.92          | ~ (v3_tex_2 @ X54 @ X55)
% 0.72/0.92          | ~ (l1_pre_topc @ X55)
% 0.72/0.92          | ~ (v2_pre_topc @ X55)
% 0.72/0.92          | (v2_struct_0 @ X55))),
% 0.72/0.92      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.72/0.92  thf('6', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_A)
% 0.72/0.92        | ~ (v2_pre_topc @ sk_A)
% 0.72/0.92        | ~ (l1_pre_topc @ sk_A)
% 0.72/0.92        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.72/0.92        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.92  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('9', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_A)
% 0.72/0.92        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.72/0.92        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.72/0.92  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('11', plain,
% 0.72/0.92      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.72/0.92      inference('clc', [status(thm)], ['9', '10'])).
% 0.72/0.92  thf('12', plain,
% 0.72/0.92      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.72/0.92  thf(d8_tex_2, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( m1_pre_topc @ B @ A ) =>
% 0.72/0.92           ( ( v4_tex_2 @ B @ A ) <=>
% 0.72/0.92             ( ![C:$i]:
% 0.72/0.92               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.72/0.92                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.72/0.92  thf('13', plain,
% 0.72/0.92      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X51 @ X52)
% 0.72/0.92          | ~ (v4_tex_2 @ X51 @ X52)
% 0.72/0.92          | ((X53) != (u1_struct_0 @ X51))
% 0.72/0.92          | (v3_tex_2 @ X53 @ X52)
% 0.72/0.92          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.72/0.92          | ~ (l1_pre_topc @ X52)
% 0.72/0.92          | (v2_struct_0 @ X52))),
% 0.72/0.92      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.72/0.92  thf('14', plain,
% 0.72/0.92      (![X51 : $i, X52 : $i]:
% 0.72/0.92         ((v2_struct_0 @ X52)
% 0.72/0.92          | ~ (l1_pre_topc @ X52)
% 0.72/0.92          | ~ (m1_subset_1 @ (u1_struct_0 @ X51) @ 
% 0.72/0.92               (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.72/0.92          | (v3_tex_2 @ (u1_struct_0 @ X51) @ X52)
% 0.72/0.92          | ~ (v4_tex_2 @ X51 @ X52)
% 0.72/0.92          | ~ (m1_pre_topc @ X51 @ X52))),
% 0.72/0.92      inference('simplify', [status(thm)], ['13'])).
% 0.72/0.92  thf('15', plain,
% 0.72/0.92      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.72/0.92        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.72/0.92        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.72/0.92        | ~ (l1_pre_topc @ sk_A)
% 0.72/0.92        | (v2_struct_0 @ sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['12', '14'])).
% 0.72/0.92  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('17', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('19', plain,
% 0.72/0.92      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.72/0.92      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.72/0.92  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('21', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.72/0.92      inference('clc', [status(thm)], ['19', '20'])).
% 0.72/0.92  thf('22', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['11', '21'])).
% 0.72/0.92  thf(d1_xboole_0, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.72/0.92  thf('23', plain,
% 0.72/0.92      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.72/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.92  thf('24', plain,
% 0.72/0.92      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.72/0.92  thf(t3_subset, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.92  thf('25', plain,
% 0.72/0.92      (![X35 : $i, X36 : $i]:
% 0.72/0.92         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.72/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.72/0.92  thf('26', plain,
% 0.72/0.92      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['24', '25'])).
% 0.72/0.92  thf(d3_tarski, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( r1_tarski @ A @ B ) <=>
% 0.72/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.72/0.92  thf('27', plain,
% 0.72/0.92      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X3 @ X4)
% 0.72/0.92          | (r2_hidden @ X3 @ X5)
% 0.72/0.92          | ~ (r1_tarski @ X4 @ X5))),
% 0.72/0.92      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.92  thf('28', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.92  thf('29', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | (r2_hidden @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['23', '28'])).
% 0.72/0.92  thf('30', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.92  thf('31', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.92  thf('32', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('33', plain, (((sk_D) = (sk_E))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('34', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('demod', [status(thm)], ['32', '33'])).
% 0.72/0.92  thf(redefinition_k6_domain_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.72/0.92       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.72/0.92  thf('35', plain,
% 0.72/0.92      (![X44 : $i, X45 : $i]:
% 0.72/0.92         ((v1_xboole_0 @ X44)
% 0.72/0.92          | ~ (m1_subset_1 @ X45 @ X44)
% 0.72/0.92          | ((k6_domain_1 @ X44 @ X45) = (k1_tarski @ X45)))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.72/0.92  thf('36', plain,
% 0.72/0.92      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['34', '35'])).
% 0.72/0.92  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('38', plain,
% 0.72/0.92      (![X44 : $i, X45 : $i]:
% 0.72/0.92         ((v1_xboole_0 @ X44)
% 0.72/0.92          | ~ (m1_subset_1 @ X45 @ X44)
% 0.72/0.92          | ((k6_domain_1 @ X44 @ X45) = (k1_tarski @ X45)))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.72/0.92  thf('39', plain,
% 0.72/0.92      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['37', '38'])).
% 0.72/0.92  thf('40', plain,
% 0.72/0.92      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.72/0.92         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('41', plain, (((sk_D) = (sk_E))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('42', plain,
% 0.72/0.92      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.72/0.92         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.72/0.92      inference('demod', [status(thm)], ['40', '41'])).
% 0.72/0.92  thf('43', plain,
% 0.72/0.92      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92          sk_C_2 @ (k1_tarski @ sk_D))
% 0.72/0.92          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['39', '42'])).
% 0.72/0.92  thf('44', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('45', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(dt_k7_domain_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) & 
% 0.72/0.92         ( m1_subset_1 @ C @ A ) ) =>
% 0.72/0.92       ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.72/0.92  thf('46', plain,
% 0.72/0.92      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X41 @ X42)
% 0.72/0.92          | (v1_xboole_0 @ X42)
% 0.72/0.92          | ~ (m1_subset_1 @ X43 @ X42)
% 0.72/0.92          | (m1_subset_1 @ (k7_domain_1 @ X42 @ X41 @ X43) @ 
% 0.72/0.92             (k1_zfmisc_1 @ X42)))),
% 0.72/0.92      inference('cnf', [status(esa)], [dt_k7_domain_1])).
% 0.72/0.92  thf('47', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ X0) @ 
% 0.72/0.92           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.72/0.92          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['45', '46'])).
% 0.72/0.92  thf('48', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | (m1_subset_1 @ 
% 0.72/0.92           (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['44', '47'])).
% 0.72/0.92  thf('49', plain,
% 0.72/0.92      (![X35 : $i, X36 : $i]:
% 0.72/0.92         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.72/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.72/0.92  thf('50', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | (r1_tarski @ (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92           (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['48', '49'])).
% 0.72/0.92  thf('51', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('52', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(redefinition_k7_domain_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) & 
% 0.72/0.92         ( m1_subset_1 @ C @ A ) ) =>
% 0.72/0.92       ( ( k7_domain_1 @ A @ B @ C ) = ( k2_tarski @ B @ C ) ) ))).
% 0.72/0.92  thf('53', plain,
% 0.72/0.92      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X46 @ X47)
% 0.72/0.92          | (v1_xboole_0 @ X47)
% 0.72/0.92          | ~ (m1_subset_1 @ X48 @ X47)
% 0.72/0.92          | ((k7_domain_1 @ X47 @ X46 @ X48) = (k2_tarski @ X46 @ X48)))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_k7_domain_1])).
% 0.72/0.92  thf('54', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (((k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ X0)
% 0.72/0.92            = (k2_tarski @ sk_D @ X0))
% 0.72/0.92          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['52', '53'])).
% 0.72/0.92  thf('55', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['11', '21'])).
% 0.72/0.92  thf('56', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92          | ((k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ X0)
% 0.72/0.92              = (k2_tarski @ sk_D @ X0)))),
% 0.72/0.92      inference('clc', [status(thm)], ['54', '55'])).
% 0.72/0.92  thf('57', plain,
% 0.72/0.92      (((k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D)
% 0.72/0.92         = (k2_tarski @ sk_D @ sk_D))),
% 0.72/0.92      inference('sup-', [status(thm)], ['51', '56'])).
% 0.72/0.92  thf(t69_enumset1, axiom,
% 0.72/0.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.72/0.92  thf('58', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.72/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.92  thf('59', plain,
% 0.72/0.92      (((k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D)
% 0.72/0.92         = (k1_tarski @ sk_D))),
% 0.72/0.92      inference('demod', [status(thm)], ['57', '58'])).
% 0.72/0.92  thf('60', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['50', '59'])).
% 0.72/0.92  thf('61', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['11', '21'])).
% 0.72/0.92  thf('62', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('clc', [status(thm)], ['60', '61'])).
% 0.72/0.92  thf('63', plain,
% 0.72/0.92      (![X35 : $i, X37 : $i]:
% 0.72/0.92         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 0.72/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.72/0.92  thf('64', plain,
% 0.72/0.92      ((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.72/0.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['62', '63'])).
% 0.72/0.92  thf('65', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_C_2 @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(t76_tex_2, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.72/0.92         ( l1_pre_topc @ A ) ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.72/0.92             ( m1_pre_topc @ B @ A ) ) =>
% 0.72/0.92           ( ![C:$i]:
% 0.72/0.92             ( ( ( v1_funct_1 @ C ) & 
% 0.72/0.92                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.72/0.92                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.72/0.92                 ( m1_subset_1 @
% 0.72/0.92                   C @ 
% 0.72/0.92                   ( k1_zfmisc_1 @
% 0.72/0.92                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.72/0.92               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.72/0.92                 ( ![D:$i]:
% 0.72/0.92                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.72/0.92                     ( ![E:$i]:
% 0.72/0.92                       ( ( m1_subset_1 @
% 0.72/0.92                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.72/0.92                         ( ( ( D ) = ( E ) ) =>
% 0.72/0.92                           ( ( k8_relset_1 @
% 0.72/0.92                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.72/0.92                               D ) =
% 0.72/0.92                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.72/0.92  thf('66', plain,
% 0.72/0.92      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.72/0.92         ((v2_struct_0 @ X56)
% 0.72/0.92          | ~ (v4_tex_2 @ X56 @ X57)
% 0.72/0.92          | ~ (m1_pre_topc @ X56 @ X57)
% 0.72/0.92          | ~ (v3_borsuk_1 @ X58 @ X57 @ X56)
% 0.72/0.92          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.72/0.92          | ((X59) != (X60))
% 0.72/0.92          | ((k8_relset_1 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56) @ X58 @ 
% 0.72/0.92              X59) = (k2_pre_topc @ X57 @ X60))
% 0.72/0.92          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.72/0.92          | ~ (m1_subset_1 @ X58 @ 
% 0.72/0.92               (k1_zfmisc_1 @ 
% 0.72/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56))))
% 0.72/0.92          | ~ (v5_pre_topc @ X58 @ X57 @ X56)
% 0.72/0.92          | ~ (v1_funct_2 @ X58 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56))
% 0.72/0.92          | ~ (v1_funct_1 @ X58)
% 0.72/0.92          | ~ (l1_pre_topc @ X57)
% 0.72/0.92          | ~ (v3_tdlat_3 @ X57)
% 0.72/0.92          | ~ (v2_pre_topc @ X57)
% 0.72/0.92          | (v2_struct_0 @ X57))),
% 0.72/0.92      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.72/0.92  thf('67', plain,
% 0.72/0.92      (![X56 : $i, X57 : $i, X58 : $i, X60 : $i]:
% 0.72/0.92         ((v2_struct_0 @ X57)
% 0.72/0.92          | ~ (v2_pre_topc @ X57)
% 0.72/0.92          | ~ (v3_tdlat_3 @ X57)
% 0.72/0.92          | ~ (l1_pre_topc @ X57)
% 0.72/0.92          | ~ (v1_funct_1 @ X58)
% 0.72/0.92          | ~ (v1_funct_2 @ X58 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56))
% 0.72/0.92          | ~ (v5_pre_topc @ X58 @ X57 @ X56)
% 0.72/0.92          | ~ (m1_subset_1 @ X58 @ 
% 0.72/0.92               (k1_zfmisc_1 @ 
% 0.72/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56))))
% 0.72/0.92          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.72/0.92          | ((k8_relset_1 @ (u1_struct_0 @ X57) @ (u1_struct_0 @ X56) @ X58 @ 
% 0.72/0.92              X60) = (k2_pre_topc @ X57 @ X60))
% 0.72/0.92          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.72/0.92          | ~ (v3_borsuk_1 @ X58 @ X57 @ X56)
% 0.72/0.92          | ~ (m1_pre_topc @ X56 @ X57)
% 0.72/0.92          | ~ (v4_tex_2 @ X56 @ X57)
% 0.72/0.92          | (v2_struct_0 @ X56))),
% 0.72/0.92      inference('simplify', [status(thm)], ['66'])).
% 0.72/0.92  thf('68', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((v2_struct_0 @ sk_B_1)
% 0.72/0.92          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.72/0.92          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.72/0.92          | ~ (v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.72/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.72/0.92          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.72/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.72/0.92          | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 0.72/0.92          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92               (u1_struct_0 @ sk_B_1))
% 0.72/0.92          | ~ (v1_funct_1 @ sk_C_2)
% 0.72/0.92          | ~ (l1_pre_topc @ sk_A)
% 0.72/0.92          | ~ (v3_tdlat_3 @ sk_A)
% 0.72/0.92          | ~ (v2_pre_topc @ sk_A)
% 0.72/0.92          | (v2_struct_0 @ sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['65', '67'])).
% 0.72/0.92  thf('69', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('70', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('71', plain, ((v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('72', plain, ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('73', plain,
% 0.72/0.92      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('74', plain, ((v1_funct_1 @ sk_C_2)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('76', plain, ((v3_tdlat_3 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('78', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((v2_struct_0 @ sk_B_1)
% 0.72/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.72/0.92          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.72/0.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.72/0.92          | (v2_struct_0 @ sk_A))),
% 0.72/0.92      inference('demod', [status(thm)],
% 0.72/0.92                ['68', '69', '70', '71', '72', '73', '74', '75', '76', '77'])).
% 0.72/0.92  thf('79', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_A)
% 0.72/0.92        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.72/0.92             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.72/0.92        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92            sk_C_2 @ (k1_tarski @ sk_D))
% 0.72/0.92            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.72/0.92        | (v2_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['64', '78'])).
% 0.72/0.92  thf('80', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('81', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92        | (m1_subset_1 @ 
% 0.72/0.92           (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['44', '47'])).
% 0.72/0.92  thf(t39_pre_topc, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( l1_pre_topc @ A ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( m1_pre_topc @ B @ A ) =>
% 0.72/0.92           ( ![C:$i]:
% 0.72/0.92             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.72/0.92               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.72/0.92  thf('82', plain,
% 0.72/0.92      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X38 @ X39)
% 0.72/0.92          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.72/0.92          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.72/0.92          | ~ (l1_pre_topc @ X39))),
% 0.72/0.92      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.72/0.92  thf('83', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.72/0.92          | ~ (l1_pre_topc @ X0)
% 0.72/0.92          | (m1_subset_1 @ 
% 0.72/0.92             (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.72/0.92          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['81', '82'])).
% 0.72/0.92  thf('84', plain,
% 0.72/0.92      (((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.72/0.92        | ~ (l1_pre_topc @ sk_A)
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['80', '83'])).
% 0.72/0.92  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('86', plain,
% 0.72/0.92      (((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['84', '85'])).
% 0.72/0.92  thf('87', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['11', '21'])).
% 0.72/0.92  thf('88', plain,
% 0.72/0.92      ((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D) @ 
% 0.72/0.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('clc', [status(thm)], ['86', '87'])).
% 0.72/0.92  thf('89', plain,
% 0.72/0.92      (((k7_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D @ sk_D)
% 0.72/0.92         = (k1_tarski @ sk_D))),
% 0.72/0.92      inference('demod', [status(thm)], ['57', '58'])).
% 0.72/0.92  thf('90', plain,
% 0.72/0.92      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('demod', [status(thm)], ['88', '89'])).
% 0.72/0.92  thf('91', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_A)
% 0.72/0.92        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92            sk_C_2 @ (k1_tarski @ sk_D))
% 0.72/0.92            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.72/0.92        | (v2_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['79', '90'])).
% 0.72/0.92  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('93', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_B_1)
% 0.72/0.92        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92            sk_C_2 @ (k1_tarski @ sk_D))
% 0.72/0.92            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.72/0.92      inference('clc', [status(thm)], ['91', '92'])).
% 0.72/0.92  thf('94', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('95', plain,
% 0.72/0.92      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.72/0.92         sk_C_2 @ (k1_tarski @ sk_D))
% 0.72/0.92         = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 0.72/0.92      inference('clc', [status(thm)], ['93', '94'])).
% 0.72/0.92  thf('96', plain,
% 0.72/0.92      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.72/0.92          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['43', '95'])).
% 0.72/0.92  thf('97', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['11', '21'])).
% 0.72/0.92  thf('98', plain,
% 0.72/0.92      (((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.72/0.92         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.72/0.92      inference('clc', [status(thm)], ['96', '97'])).
% 0.72/0.92  thf('99', plain,
% 0.72/0.92      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.72/0.92          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['36', '98'])).
% 0.72/0.92  thf('100', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('simplify', [status(thm)], ['99'])).
% 0.72/0.92  thf('101', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.72/0.92      inference('demod', [status(thm)], ['31', '100'])).
% 0.72/0.92  thf('102', plain, ($false), inference('demod', [status(thm)], ['22', '101'])).
% 0.72/0.92  
% 0.72/0.92  % SZS output end Refutation
% 0.72/0.92  
% 0.75/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
