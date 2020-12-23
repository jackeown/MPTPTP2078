%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nkDP8n3fJb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 144 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  638 (2230 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t33_tex_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tex_2])).

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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X35 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v2_tex_2 @ X40 @ X41 )
      | ( m1_subset_1 @ ( sk_D @ X42 @ X40 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( r1_tarski @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X44: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X44 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X44 @ sk_A )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v2_tex_2 @ X40 @ X41 )
      | ( v4_pre_topc @ ( sk_D @ X42 @ X40 @ X41 ) @ X41 )
      | ~ ( r1_tarski @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v2_tex_2 @ X40 @ X41 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( sk_D @ X42 @ X40 @ X41 ) )
        = X42 )
      | ~ ( r1_tarski @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','47'])).

thf('49',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nkDP8n3fJb
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 132 iterations in 0.076s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(t33_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.54                      ( ![D:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @
% 0.21/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.54                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( l1_pre_topc @ A ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.54                ( ![C:$i]:
% 0.21/0.54                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.54                         ( ![D:$i]:
% 0.21/0.54                           ( ( m1_subset_1 @
% 0.21/0.54                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.54                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.54                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.21/0.54  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t5_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X37 @ X38)
% 0.21/0.54          | ~ (v1_xboole_0 @ X39)
% 0.21/0.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d2_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X32 : $i, X33 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X32 @ X33)
% 0.21/0.54          | (r2_hidden @ X32 @ X33)
% 0.21/0.54          | (v1_xboole_0 @ X33))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf(t63_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X35 : $i, X36 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_tarski @ X35) @ (k1_zfmisc_1 @ X36))
% 0.21/0.54          | ~ (r2_hidden @ X35 @ X36))),
% 0.21/0.54      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d6_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.54                      ( ![D:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @
% 0.21/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.54                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (v2_tex_2 @ X40 @ X41)
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X42 @ X40 @ X41) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (r1_tarski @ X42 @ X40)
% 0.21/0.54          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (l1_pre_topc @ X41))),
% 0.21/0.54      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '14'])).
% 0.21/0.54  thf('16', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t38_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.21/0.54         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.21/0.54          | ~ (r2_hidden @ X30 @ X31)
% 0.21/0.54          | ~ (r2_hidden @ X28 @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.54          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.54  thf(t69_enumset1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.54  thf('21', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.54  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X44 : $i]:
% 0.21/0.54         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X44)
% 0.21/0.54            != (k1_tarski @ sk_C_1))
% 0.21/0.54          | ~ (v4_pre_topc @ X44 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.21/0.54            != (k1_tarski @ sk_C_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (v2_tex_2 @ X40 @ X41)
% 0.21/0.54          | (v4_pre_topc @ (sk_D @ X42 @ X40 @ X41) @ X41)
% 0.21/0.54          | ~ (r1_tarski @ X42 @ X40)
% 0.21/0.54          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (l1_pre_topc @ X41))),
% 0.21/0.54      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.54          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.54          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.54          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.54  thf('34', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['25', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (v2_tex_2 @ X40 @ X41)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 0.21/0.54              (sk_D @ X42 @ X40 @ X41)) = (X42))
% 0.21/0.54          | ~ (r1_tarski @ X42 @ X40)
% 0.21/0.54          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.54          | ~ (l1_pre_topc @ X41))),
% 0.21/0.54      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.21/0.54          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.21/0.54        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '43'])).
% 0.21/0.54  thf('45', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.54            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['36', '46'])).
% 0.21/0.54  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '47'])).
% 0.21/0.54  thf('49', plain, ($false), inference('sup-', [status(thm)], ['0', '48'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
