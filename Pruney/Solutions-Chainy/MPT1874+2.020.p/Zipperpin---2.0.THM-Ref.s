%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HDggxic7gZ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:44 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 248 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  922 (4265 expanded)
%              Number of equality atoms :   36 ( 139 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t42_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( v1_xboole_0 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X52: $i,X53: $i] :
      ( ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ X52 )
      | ( ( k6_domain_1 @ X52 @ X53 )
        = ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k9_subset_1 @ X28 @ X30 @ X29 )
        = ( k9_subset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k9_subset_1 @ X39 @ X37 @ X38 )
        = ( k3_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ sk_B )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 @ ( sk_D_1 @ X56 @ X54 @ X55 ) )
        = ( k1_tarski @ X56 ) )
      | ~ ( r2_hidden @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X56 @ ( u1_struct_0 @ X55 ) )
      | ~ ( v2_tex_2 @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t33_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( m1_subset_1 @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( v2_tex_2 @ X57 @ X58 )
      | ~ ( r1_tarski @ X59 @ X57 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_pre_topc @ X58 @ X59 ) )
        = X59 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('42',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('48',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( r1_tarski @ X42 @ X40 )
      | ( r2_hidden @ ( sk_D @ X40 @ X42 @ X41 ) @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( r1_tarski @ X42 @ X40 )
      | ~ ( r2_hidden @ ( sk_D @ X40 @ X42 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(simplify,[status(thm)],['56'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_B @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ sk_B @ X0 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k9_subset_1 @ X39 @ X37 @ X38 )
        = ( k3_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_B @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['45','67'])).

thf('69',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ sk_B )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_tarski @ sk_C_1 )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','71'])).

thf('73',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('74',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','74'])).

thf('76',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HDggxic7gZ
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.81  % Solved by: fo/fo7.sh
% 0.62/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.81  % done 659 iterations in 0.353s
% 0.62/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.81  % SZS output start Refutation
% 0.62/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.62/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.62/0.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.62/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.81  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.62/0.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.62/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.81  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.62/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.62/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.62/0.81  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.62/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.81  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.62/0.81  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.62/0.81  thf(t42_tex_2, conjecture,
% 0.62/0.81    (![A:$i]:
% 0.62/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.62/0.81       ( ![B:$i]:
% 0.62/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.81           ( ( v2_tex_2 @ B @ A ) =>
% 0.62/0.81             ( ![C:$i]:
% 0.62/0.81               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.81                 ( ( r2_hidden @ C @ B ) =>
% 0.62/0.81                   ( ( k9_subset_1 @
% 0.62/0.81                       ( u1_struct_0 @ A ) @ B @ 
% 0.62/0.81                       ( k2_pre_topc @
% 0.62/0.81                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.62/0.81                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.62/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.81    (~( ![A:$i]:
% 0.62/0.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.62/0.81            ( l1_pre_topc @ A ) ) =>
% 0.62/0.81          ( ![B:$i]:
% 0.62/0.81            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.81              ( ( v2_tex_2 @ B @ A ) =>
% 0.62/0.81                ( ![C:$i]:
% 0.62/0.81                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.81                    ( ( r2_hidden @ C @ B ) =>
% 0.62/0.81                      ( ( k9_subset_1 @
% 0.62/0.81                          ( u1_struct_0 @ A ) @ B @ 
% 0.62/0.81                          ( k2_pre_topc @
% 0.62/0.81                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.62/0.81                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.62/0.81    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.62/0.81  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('1', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(t5_subset, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.62/0.81          ( v1_xboole_0 @ C ) ) ))).
% 0.62/0.81  thf('2', plain,
% 0.62/0.81      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X49 @ X50)
% 0.62/0.81          | ~ (v1_xboole_0 @ X51)
% 0.62/0.81          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t5_subset])).
% 0.62/0.81  thf('3', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.81  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(redefinition_k6_domain_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.62/0.81       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.62/0.81  thf('5', plain,
% 0.62/0.81      (![X52 : $i, X53 : $i]:
% 0.62/0.81         ((v1_xboole_0 @ X52)
% 0.62/0.81          | ~ (m1_subset_1 @ X53 @ X52)
% 0.62/0.81          | ((k6_domain_1 @ X52 @ X53) = (k1_tarski @ X53)))),
% 0.62/0.81      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.62/0.81  thf('6', plain,
% 0.62/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.62/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.81  thf('7', plain,
% 0.62/0.81      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.62/0.81         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.62/0.81         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('8', plain,
% 0.62/0.81      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.62/0.81          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.62/0.81          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.62/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.81  thf('9', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(commutativity_k9_subset_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.62/0.81  thf('10', plain,
% 0.62/0.81      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.62/0.81         (((k9_subset_1 @ X28 @ X30 @ X29) = (k9_subset_1 @ X28 @ X29 @ X30))
% 0.62/0.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.62/0.81      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.62/0.81  thf('11', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.62/0.81           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.81  thf('12', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(redefinition_k9_subset_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.62/0.81  thf('13', plain,
% 0.62/0.81      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.62/0.81         (((k9_subset_1 @ X39 @ X37 @ X38) = (k3_xboole_0 @ X37 @ X38))
% 0.62/0.81          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.62/0.81      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.62/0.81  thf('14', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.62/0.81           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.62/0.81  thf('15', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k3_xboole_0 @ X0 @ sk_B)
% 0.62/0.81           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['11', '14'])).
% 0.62/0.81  thf('16', plain,
% 0.62/0.81      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ sk_B)
% 0.62/0.81          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.62/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('demod', [status(thm)], ['8', '15'])).
% 0.62/0.81  thf('17', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('18', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(t33_tex_2, axiom,
% 0.62/0.81    (![A:$i]:
% 0.62/0.81     ( ( l1_pre_topc @ A ) =>
% 0.62/0.81       ( ![B:$i]:
% 0.62/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.81           ( ( v2_tex_2 @ B @ A ) =>
% 0.62/0.81             ( ![C:$i]:
% 0.62/0.81               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.81                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.62/0.81                      ( ![D:$i]:
% 0.62/0.81                        ( ( m1_subset_1 @
% 0.62/0.81                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.81                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.62/0.81                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.62/0.81                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.62/0.81  thf('19', plain,
% 0.62/0.81      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.62/0.81          | ((k9_subset_1 @ (u1_struct_0 @ X55) @ X54 @ 
% 0.62/0.81              (sk_D_1 @ X56 @ X54 @ X55)) = (k1_tarski @ X56))
% 0.62/0.81          | ~ (r2_hidden @ X56 @ X54)
% 0.62/0.81          | ~ (m1_subset_1 @ X56 @ (u1_struct_0 @ X55))
% 0.62/0.81          | ~ (v2_tex_2 @ X54 @ X55)
% 0.62/0.81          | ~ (l1_pre_topc @ X55))),
% 0.62/0.81      inference('cnf', [status(esa)], [t33_tex_2])).
% 0.62/0.81  thf('20', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (l1_pre_topc @ sk_A)
% 0.62/0.81          | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.62/0.81          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.81          | ~ (r2_hidden @ X0 @ sk_B)
% 0.62/0.81          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.62/0.81              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (k1_tarski @ X0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['18', '19'])).
% 0.62/0.81  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('22', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('23', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k3_xboole_0 @ X0 @ sk_B)
% 0.62/0.81           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['11', '14'])).
% 0.62/0.81  thf('24', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.62/0.81          | ~ (r2_hidden @ X0 @ sk_B)
% 0.62/0.81          | ((k3_xboole_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.62/0.81              = (k1_tarski @ X0)))),
% 0.62/0.81      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.62/0.81  thf('25', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(t4_subset, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.62/0.81       ( m1_subset_1 @ A @ C ) ))).
% 0.62/0.81  thf('26', plain,
% 0.62/0.81      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X46 @ X47)
% 0.62/0.81          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 0.62/0.81          | (m1_subset_1 @ X46 @ X48))),
% 0.62/0.81      inference('cnf', [status(esa)], [t4_subset])).
% 0.62/0.81  thf('27', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.81  thf('28', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (((k3_xboole_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.62/0.81            = (k1_tarski @ X0))
% 0.62/0.81          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.62/0.81      inference('clc', [status(thm)], ['24', '27'])).
% 0.62/0.81  thf('29', plain,
% 0.62/0.81      (((k3_xboole_0 @ (sk_D_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.62/0.81         = (k1_tarski @ sk_C_1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['17', '28'])).
% 0.62/0.81  thf('30', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(dt_k9_subset_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.62/0.81  thf('31', plain,
% 0.62/0.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.62/0.81         ((m1_subset_1 @ (k9_subset_1 @ X34 @ X35 @ X36) @ (k1_zfmisc_1 @ X34))
% 0.62/0.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X34)))),
% 0.62/0.81      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.62/0.81  thf('32', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.62/0.81          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['30', '31'])).
% 0.62/0.81  thf('33', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.62/0.81           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.62/0.81  thf('34', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.62/0.81          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.62/0.81  thf('35', plain,
% 0.62/0.81      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.62/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['29', '34'])).
% 0.62/0.81  thf('36', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(t41_tex_2, axiom,
% 0.62/0.81    (![A:$i]:
% 0.62/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.62/0.81       ( ![B:$i]:
% 0.62/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.81           ( ( v2_tex_2 @ B @ A ) <=>
% 0.62/0.81             ( ![C:$i]:
% 0.62/0.81               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.81                 ( ( r1_tarski @ C @ B ) =>
% 0.62/0.81                   ( ( k9_subset_1 @
% 0.62/0.81                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.62/0.81                     ( C ) ) ) ) ) ) ) ) ))).
% 0.62/0.81  thf('37', plain,
% 0.62/0.81      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.62/0.81          | ~ (v2_tex_2 @ X57 @ X58)
% 0.62/0.81          | ~ (r1_tarski @ X59 @ X57)
% 0.62/0.81          | ((k9_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 0.62/0.81              (k2_pre_topc @ X58 @ X59)) = (X59))
% 0.62/0.81          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.62/0.81          | ~ (l1_pre_topc @ X58)
% 0.62/0.81          | ~ (v2_pre_topc @ X58)
% 0.62/0.81          | (v2_struct_0 @ X58))),
% 0.62/0.81      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.62/0.81  thf('38', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((v2_struct_0 @ sk_A)
% 0.62/0.81          | ~ (v2_pre_topc @ sk_A)
% 0.62/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.62/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.81          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.62/0.81              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.62/0.81          | ~ (r1_tarski @ X0 @ sk_B)
% 0.62/0.81          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.62/0.81      inference('sup-', [status(thm)], ['36', '37'])).
% 0.62/0.81  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('41', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k3_xboole_0 @ X0 @ sk_B)
% 0.62/0.81           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['11', '14'])).
% 0.62/0.81  thf('42', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('43', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((v2_struct_0 @ sk_A)
% 0.62/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.81          | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_B) = (X0))
% 0.62/0.81          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.62/0.81      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.62/0.81  thf('44', plain,
% 0.62/0.81      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.62/0.81        | ((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ sk_B)
% 0.62/0.81            = (k1_tarski @ sk_C_1))
% 0.62/0.81        | (v2_struct_0 @ sk_A))),
% 0.62/0.81      inference('sup-', [status(thm)], ['35', '43'])).
% 0.62/0.81  thf('45', plain,
% 0.62/0.81      (((k3_xboole_0 @ (sk_D_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.62/0.81         = (k1_tarski @ sk_C_1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['17', '28'])).
% 0.62/0.81  thf('46', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('47', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(t7_subset_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81       ( ![C:$i]:
% 0.62/0.81         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81           ( ( ![D:$i]:
% 0.62/0.81               ( ( m1_subset_1 @ D @ A ) =>
% 0.62/0.81                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.62/0.81             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.62/0.81  thf('48', plain,
% 0.62/0.81      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.62/0.81          | (r1_tarski @ X42 @ X40)
% 0.62/0.81          | (r2_hidden @ (sk_D @ X40 @ X42 @ X41) @ X42)
% 0.62/0.81          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.62/0.81  thf('49', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.81          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.62/0.81          | (r1_tarski @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.81  thf('50', plain,
% 0.62/0.81      (((r1_tarski @ sk_B @ sk_B)
% 0.62/0.81        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['46', '49'])).
% 0.62/0.81  thf('51', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('52', plain,
% 0.62/0.81      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.62/0.81          | (r1_tarski @ X42 @ X40)
% 0.62/0.81          | ~ (r2_hidden @ (sk_D @ X40 @ X42 @ X41) @ X40)
% 0.62/0.81          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.62/0.81  thf('53', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.81          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.62/0.81          | (r1_tarski @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['51', '52'])).
% 0.62/0.81  thf('54', plain,
% 0.62/0.81      (((r1_tarski @ sk_B @ sk_B)
% 0.62/0.81        | (r1_tarski @ sk_B @ sk_B)
% 0.62/0.81        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.62/0.81      inference('sup-', [status(thm)], ['50', '53'])).
% 0.62/0.81  thf('55', plain,
% 0.62/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('56', plain, (((r1_tarski @ sk_B @ sk_B) | (r1_tarski @ sk_B @ sk_B))),
% 0.62/0.81      inference('demod', [status(thm)], ['54', '55'])).
% 0.62/0.81  thf('57', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.62/0.81      inference('simplify', [status(thm)], ['56'])).
% 0.62/0.81  thf(t3_subset, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.81  thf('58', plain,
% 0.62/0.81      (![X43 : $i, X45 : $i]:
% 0.62/0.81         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.81  thf('59', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.62/0.81  thf('60', plain,
% 0.62/0.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.62/0.81         ((m1_subset_1 @ (k9_subset_1 @ X34 @ X35 @ X36) @ (k1_zfmisc_1 @ X34))
% 0.62/0.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X34)))),
% 0.62/0.81      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.62/0.81  thf('61', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (m1_subset_1 @ (k9_subset_1 @ sk_B @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.81  thf('62', plain,
% 0.62/0.81      (![X43 : $i, X44 : $i]:
% 0.62/0.81         ((r1_tarski @ X43 @ X44) | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.81  thf('63', plain,
% 0.62/0.81      (![X0 : $i]: (r1_tarski @ (k9_subset_1 @ sk_B @ X0 @ sk_B) @ sk_B)),
% 0.62/0.81      inference('sup-', [status(thm)], ['61', '62'])).
% 0.62/0.81  thf('64', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.62/0.81  thf('65', plain,
% 0.62/0.81      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.62/0.81         (((k9_subset_1 @ X39 @ X37 @ X38) = (k3_xboole_0 @ X37 @ X38))
% 0.62/0.81          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.62/0.81      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.62/0.81  thf('66', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         ((k9_subset_1 @ sk_B @ X0 @ sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['64', '65'])).
% 0.62/0.81  thf('67', plain,
% 0.62/0.81      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)),
% 0.62/0.81      inference('demod', [status(thm)], ['63', '66'])).
% 0.62/0.81  thf('68', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.62/0.81      inference('sup+', [status(thm)], ['45', '67'])).
% 0.62/0.81  thf('69', plain,
% 0.62/0.81      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ sk_B)
% 0.62/0.81          = (k1_tarski @ sk_C_1))
% 0.62/0.81        | (v2_struct_0 @ sk_A))),
% 0.62/0.81      inference('demod', [status(thm)], ['44', '68'])).
% 0.62/0.81  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('71', plain,
% 0.62/0.81      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)) @ sk_B)
% 0.62/0.81         = (k1_tarski @ sk_C_1))),
% 0.62/0.81      inference('clc', [status(thm)], ['69', '70'])).
% 0.62/0.81  thf('72', plain,
% 0.62/0.81      ((((k1_tarski @ sk_C_1) != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.62/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('demod', [status(thm)], ['16', '71'])).
% 0.62/0.81  thf('73', plain,
% 0.62/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.62/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.81  thf('74', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.62/0.81      inference('clc', [status(thm)], ['72', '73'])).
% 0.62/0.81  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.62/0.81      inference('demod', [status(thm)], ['3', '74'])).
% 0.62/0.81  thf('76', plain, ($false), inference('sup-', [status(thm)], ['0', '75'])).
% 0.62/0.81  
% 0.62/0.81  % SZS output end Refutation
% 0.62/0.81  
% 0.62/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
