%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SHAkh86Ioa

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:33 EST 2020

% Result     : Theorem 18.53s
% Output     : Refutation 18.53s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 179 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  637 (2003 expanded)
%              Number of equality atoms :   29 (  94 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t33_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v3_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tops_2])).

thf('0',plain,(
    ~ ( v3_pre_topc @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_2 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_D_2 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_C ) @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_C ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_C ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('18',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t32_tops_2,axiom,(
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

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X23 @ ( k2_struct_0 @ X20 ) )
       != X22 )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X23 @ ( k2_struct_0 @ X20 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X23 @ ( k2_struct_0 @ X20 ) ) @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('40',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( v3_pre_topc @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('49',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('50',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('51',plain,(
    v3_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['2','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SHAkh86Ioa
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.53/18.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.53/18.73  % Solved by: fo/fo7.sh
% 18.53/18.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.53/18.73  % done 9082 iterations in 18.280s
% 18.53/18.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.53/18.73  % SZS output start Refutation
% 18.53/18.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.53/18.73  thf(sk_A_type, type, sk_A: $i).
% 18.53/18.73  thf(sk_D_2_type, type, sk_D_2: $i).
% 18.53/18.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.53/18.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 18.53/18.73  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 18.53/18.73  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 18.53/18.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.53/18.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 18.53/18.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 18.53/18.73  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 18.53/18.73  thf(sk_C_type, type, sk_C: $i).
% 18.53/18.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 18.53/18.73  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 18.53/18.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 18.53/18.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.53/18.73  thf(sk_B_type, type, sk_B: $i).
% 18.53/18.73  thf(t33_tops_2, conjecture,
% 18.53/18.73    (![A:$i]:
% 18.53/18.73     ( ( l1_pre_topc @ A ) =>
% 18.53/18.73       ( ![B:$i]:
% 18.53/18.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.53/18.73           ( ![C:$i]:
% 18.53/18.73             ( ( m1_pre_topc @ C @ A ) =>
% 18.53/18.73               ( ( v3_pre_topc @ B @ A ) =>
% 18.53/18.73                 ( ![D:$i]:
% 18.53/18.73                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 18.53/18.73                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 18.53/18.73  thf(zf_stmt_0, negated_conjecture,
% 18.53/18.73    (~( ![A:$i]:
% 18.53/18.73        ( ( l1_pre_topc @ A ) =>
% 18.53/18.73          ( ![B:$i]:
% 18.53/18.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.53/18.73              ( ![C:$i]:
% 18.53/18.73                ( ( m1_pre_topc @ C @ A ) =>
% 18.53/18.73                  ( ( v3_pre_topc @ B @ A ) =>
% 18.53/18.73                    ( ![D:$i]:
% 18.53/18.73                      ( ( m1_subset_1 @
% 18.53/18.73                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 18.53/18.73                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 18.53/18.73    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 18.53/18.73  thf('0', plain, (~ (v3_pre_topc @ sk_D_2 @ sk_C)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('1', plain, (((sk_D_2) = (sk_B))),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C)),
% 18.53/18.73      inference('demod', [status(thm)], ['0', '1'])).
% 18.53/18.73  thf(d3_struct_0, axiom,
% 18.53/18.73    (![A:$i]:
% 18.53/18.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 18.53/18.73  thf('3', plain,
% 18.53/18.73      (![X16 : $i]:
% 18.53/18.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 18.53/18.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 18.53/18.73  thf('4', plain,
% 18.53/18.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('5', plain,
% 18.53/18.73      (![X16 : $i]:
% 18.53/18.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 18.53/18.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 18.53/18.73  thf(d4_xboole_0, axiom,
% 18.53/18.73    (![A:$i,B:$i,C:$i]:
% 18.53/18.73     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 18.53/18.73       ( ![D:$i]:
% 18.53/18.73         ( ( r2_hidden @ D @ C ) <=>
% 18.53/18.73           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 18.53/18.73  thf('6', plain,
% 18.53/18.73      (![X1 : $i, X2 : $i, X5 : $i]:
% 18.53/18.73         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 18.53/18.73          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 18.53/18.73          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 18.53/18.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 18.53/18.73  thf('7', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]:
% 18.53/18.73         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 18.53/18.73          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 18.53/18.73      inference('eq_fact', [status(thm)], ['6'])).
% 18.53/18.73  thf('8', plain,
% 18.53/18.73      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('9', plain, (((sk_D_2) = (sk_B))),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('10', plain,
% 18.53/18.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 18.53/18.73      inference('demod', [status(thm)], ['8', '9'])).
% 18.53/18.73  thf(l3_subset_1, axiom,
% 18.53/18.73    (![A:$i,B:$i]:
% 18.53/18.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 18.53/18.73       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 18.53/18.73  thf('11', plain,
% 18.53/18.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 18.53/18.73         (~ (r2_hidden @ X8 @ X9)
% 18.53/18.73          | (r2_hidden @ X8 @ X10)
% 18.53/18.73          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 18.53/18.73      inference('cnf', [status(esa)], [l3_subset_1])).
% 18.53/18.73  thf('12', plain,
% 18.53/18.73      (![X0 : $i]:
% 18.53/18.73         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C)) | ~ (r2_hidden @ X0 @ sk_B))),
% 18.53/18.73      inference('sup-', [status(thm)], ['10', '11'])).
% 18.53/18.73  thf('13', plain,
% 18.53/18.73      (![X0 : $i]:
% 18.53/18.73         (((sk_B) = (k3_xboole_0 @ sk_B @ X0))
% 18.53/18.73          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 18.53/18.73      inference('sup-', [status(thm)], ['7', '12'])).
% 18.53/18.73  thf('14', plain,
% 18.53/18.73      (![X1 : $i, X2 : $i, X5 : $i]:
% 18.53/18.73         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 18.53/18.73          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 18.53/18.73          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 18.53/18.73          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 18.53/18.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 18.53/18.73  thf('15', plain,
% 18.53/18.73      ((((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C)))
% 18.53/18.73        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_C) @ sk_B) @ sk_B)
% 18.53/18.73        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_C) @ sk_B) @ sk_B)
% 18.53/18.73        | ((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C))))),
% 18.53/18.73      inference('sup-', [status(thm)], ['13', '14'])).
% 18.53/18.73  thf('16', plain,
% 18.53/18.73      ((~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_C) @ sk_B) @ sk_B)
% 18.53/18.73        | ((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C))))),
% 18.53/18.73      inference('simplify', [status(thm)], ['15'])).
% 18.53/18.73  thf('17', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]:
% 18.53/18.73         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 18.53/18.73          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 18.53/18.73      inference('eq_fact', [status(thm)], ['6'])).
% 18.53/18.73  thf('18', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C)))),
% 18.53/18.73      inference('clc', [status(thm)], ['16', '17'])).
% 18.53/18.73  thf('19', plain,
% 18.53/18.73      ((((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))
% 18.53/18.73        | ~ (l1_struct_0 @ sk_C))),
% 18.53/18.73      inference('sup+', [status(thm)], ['5', '18'])).
% 18.53/18.73  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf(dt_m1_pre_topc, axiom,
% 18.53/18.73    (![A:$i]:
% 18.53/18.73     ( ( l1_pre_topc @ A ) =>
% 18.53/18.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 18.53/18.73  thf('21', plain,
% 18.53/18.73      (![X18 : $i, X19 : $i]:
% 18.53/18.73         (~ (m1_pre_topc @ X18 @ X19)
% 18.53/18.73          | (l1_pre_topc @ X18)
% 18.53/18.73          | ~ (l1_pre_topc @ X19))),
% 18.53/18.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 18.53/18.73  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 18.53/18.73      inference('sup-', [status(thm)], ['20', '21'])).
% 18.53/18.73  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 18.53/18.73      inference('demod', [status(thm)], ['22', '23'])).
% 18.53/18.73  thf(dt_l1_pre_topc, axiom,
% 18.53/18.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 18.53/18.73  thf('25', plain,
% 18.53/18.73      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 18.53/18.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 18.53/18.73  thf('26', plain, ((l1_struct_0 @ sk_C)),
% 18.53/18.73      inference('sup-', [status(thm)], ['24', '25'])).
% 18.53/18.73  thf('27', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))),
% 18.53/18.73      inference('demod', [status(thm)], ['19', '26'])).
% 18.53/18.73  thf('28', plain,
% 18.53/18.73      (![X16 : $i]:
% 18.53/18.73         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 18.53/18.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 18.53/18.73  thf(t32_tops_2, axiom,
% 18.53/18.73    (![A:$i]:
% 18.53/18.73     ( ( l1_pre_topc @ A ) =>
% 18.53/18.73       ( ![B:$i]:
% 18.53/18.73         ( ( m1_pre_topc @ B @ A ) =>
% 18.53/18.73           ( ![C:$i]:
% 18.53/18.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 18.53/18.73               ( ( v3_pre_topc @ C @ B ) <=>
% 18.53/18.73                 ( ?[D:$i]:
% 18.53/18.73                   ( ( ( k9_subset_1 @
% 18.53/18.73                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 18.53/18.73                       ( C ) ) & 
% 18.53/18.73                     ( v3_pre_topc @ D @ A ) & 
% 18.53/18.73                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 18.53/18.73  thf('29', plain,
% 18.53/18.73      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 18.53/18.73         (~ (m1_pre_topc @ X20 @ X21)
% 18.53/18.73          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X23 @ (k2_struct_0 @ X20))
% 18.53/18.73              != (X22))
% 18.53/18.73          | ~ (v3_pre_topc @ X23 @ X21)
% 18.53/18.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 18.53/18.73          | (v3_pre_topc @ X22 @ X20)
% 18.53/18.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 18.53/18.73          | ~ (l1_pre_topc @ X21))),
% 18.53/18.73      inference('cnf', [status(esa)], [t32_tops_2])).
% 18.53/18.73  thf('30', plain,
% 18.53/18.73      (![X20 : $i, X21 : $i, X23 : $i]:
% 18.53/18.73         (~ (l1_pre_topc @ X21)
% 18.53/18.73          | ~ (m1_subset_1 @ 
% 18.53/18.73               (k9_subset_1 @ (u1_struct_0 @ X20) @ X23 @ (k2_struct_0 @ X20)) @ 
% 18.53/18.73               (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 18.53/18.73          | (v3_pre_topc @ 
% 18.53/18.73             (k9_subset_1 @ (u1_struct_0 @ X20) @ X23 @ (k2_struct_0 @ X20)) @ 
% 18.53/18.73             X20)
% 18.53/18.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 18.53/18.73          | ~ (v3_pre_topc @ X23 @ X21)
% 18.53/18.73          | ~ (m1_pre_topc @ X20 @ X21))),
% 18.53/18.73      inference('simplify', [status(thm)], ['29'])).
% 18.53/18.73  thf('31', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (m1_subset_1 @ 
% 18.53/18.73             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 18.53/18.73             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 18.53/18.73          | ~ (l1_struct_0 @ X0)
% 18.53/18.73          | ~ (m1_pre_topc @ X0 @ X2)
% 18.53/18.73          | ~ (v3_pre_topc @ X1 @ X2)
% 18.53/18.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 18.53/18.73          | (v3_pre_topc @ 
% 18.53/18.73             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 18.53/18.73          | ~ (l1_pre_topc @ X2))),
% 18.53/18.73      inference('sup-', [status(thm)], ['28', '30'])).
% 18.53/18.73  thf(dt_k2_subset_1, axiom,
% 18.53/18.73    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 18.53/18.73  thf('32', plain,
% 18.53/18.73      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 18.53/18.73      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 18.53/18.73  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 18.53/18.73  thf('33', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 18.53/18.73      inference('cnf', [status(esa)], [d4_subset_1])).
% 18.53/18.73  thf('34', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 18.53/18.73      inference('demod', [status(thm)], ['32', '33'])).
% 18.53/18.73  thf(redefinition_k9_subset_1, axiom,
% 18.53/18.73    (![A:$i,B:$i,C:$i]:
% 18.53/18.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 18.53/18.73       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 18.53/18.73  thf('35', plain,
% 18.53/18.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 18.53/18.73         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 18.53/18.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 18.53/18.73      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 18.53/18.73  thf('36', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]:
% 18.53/18.73         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 18.53/18.73      inference('sup-', [status(thm)], ['34', '35'])).
% 18.53/18.73  thf('37', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.73         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 18.53/18.73             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 18.53/18.73          | ~ (l1_struct_0 @ X0)
% 18.53/18.73          | ~ (m1_pre_topc @ X0 @ X2)
% 18.53/18.73          | ~ (v3_pre_topc @ X1 @ X2)
% 18.53/18.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 18.53/18.73          | (v3_pre_topc @ 
% 18.53/18.73             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 18.53/18.73          | ~ (l1_pre_topc @ X2))),
% 18.53/18.73      inference('demod', [status(thm)], ['31', '36'])).
% 18.53/18.73  thf('38', plain,
% 18.53/18.73      (![X0 : $i]:
% 18.53/18.73         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 18.53/18.73          | ~ (l1_pre_topc @ X0)
% 18.53/18.73          | (v3_pre_topc @ 
% 18.53/18.73             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 18.53/18.73             sk_C)
% 18.53/18.73          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 18.53/18.73          | ~ (v3_pre_topc @ sk_B @ X0)
% 18.53/18.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 18.53/18.73          | ~ (l1_struct_0 @ sk_C))),
% 18.53/18.73      inference('sup-', [status(thm)], ['27', '37'])).
% 18.53/18.73  thf('39', plain,
% 18.53/18.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 18.53/18.73      inference('demod', [status(thm)], ['8', '9'])).
% 18.53/18.73  thf('40', plain, ((l1_struct_0 @ sk_C)),
% 18.53/18.73      inference('sup-', [status(thm)], ['24', '25'])).
% 18.53/18.73  thf('41', plain,
% 18.53/18.73      (![X0 : $i]:
% 18.53/18.73         (~ (l1_pre_topc @ X0)
% 18.53/18.73          | (v3_pre_topc @ 
% 18.53/18.73             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 18.53/18.73             sk_C)
% 18.53/18.73          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 18.53/18.73          | ~ (v3_pre_topc @ sk_B @ X0)
% 18.53/18.73          | ~ (m1_pre_topc @ sk_C @ X0))),
% 18.53/18.73      inference('demod', [status(thm)], ['38', '39', '40'])).
% 18.53/18.73  thf('42', plain,
% 18.53/18.73      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 18.53/18.73        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 18.53/18.73        | (v3_pre_topc @ 
% 18.53/18.73           (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 18.53/18.73           sk_C)
% 18.53/18.73        | ~ (l1_pre_topc @ sk_A))),
% 18.53/18.73      inference('sup-', [status(thm)], ['4', '41'])).
% 18.53/18.73  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('44', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 18.53/18.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.73  thf('46', plain,
% 18.53/18.73      ((v3_pre_topc @ 
% 18.53/18.73        (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 18.53/18.73        sk_C)),
% 18.53/18.73      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 18.53/18.73  thf('47', plain,
% 18.53/18.73      (((v3_pre_topc @ 
% 18.53/18.73         (k9_subset_1 @ (k2_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 18.53/18.73         sk_C)
% 18.53/18.73        | ~ (l1_struct_0 @ sk_C))),
% 18.53/18.73      inference('sup+', [status(thm)], ['3', '46'])).
% 18.53/18.73  thf('48', plain,
% 18.53/18.73      (![X0 : $i, X1 : $i]:
% 18.53/18.73         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 18.53/18.73      inference('sup-', [status(thm)], ['34', '35'])).
% 18.53/18.73  thf('49', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C)))),
% 18.53/18.73      inference('demod', [status(thm)], ['19', '26'])).
% 18.53/18.73  thf('50', plain, ((l1_struct_0 @ sk_C)),
% 18.53/18.73      inference('sup-', [status(thm)], ['24', '25'])).
% 18.53/18.73  thf('51', plain, ((v3_pre_topc @ sk_B @ sk_C)),
% 18.53/18.73      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 18.53/18.73  thf('52', plain, ($false), inference('demod', [status(thm)], ['2', '51'])).
% 18.53/18.73  
% 18.53/18.73  % SZS output end Refutation
% 18.53/18.73  
% 18.53/18.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
