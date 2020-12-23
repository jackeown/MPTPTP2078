%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w5n3Zd27Th

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:06 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  545 (1091 expanded)
%              Number of equality atoms :   45 (  89 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t25_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( ( k2_struct_0 @ A )
                    = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  & ( r1_xboole_0 @ B @ C ) )
               => ( C
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( ( k2_struct_0 @ A )
                      = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    & ( r1_xboole_0 @ B @ C ) )
                 => ( C
                    = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_pre_topc])).

thf('0',plain,(
    sk_C
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X23 @ X22 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('9',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k9_setfam_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k9_setfam_1 @ X23 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X23 @ X22 @ X24 ) @ ( k9_setfam_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('24',plain,(
    ! [X31: $i] :
      ( ( k9_setfam_1 @ X31 )
      = ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_C ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['0','19','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w5n3Zd27Th
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.04/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.24  % Solved by: fo/fo7.sh
% 1.04/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.24  % done 1074 iterations in 0.757s
% 1.04/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.24  % SZS output start Refutation
% 1.04/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.24  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.04/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.24  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 1.04/1.24  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.04/1.24  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.04/1.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.04/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.04/1.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.04/1.24  thf(t25_pre_topc, conjecture,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( l1_struct_0 @ A ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24           ( ![C:$i]:
% 1.04/1.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24               ( ( ( ( k2_struct_0 @ A ) =
% 1.04/1.24                     ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) & 
% 1.04/1.24                   ( r1_xboole_0 @ B @ C ) ) =>
% 1.04/1.24                 ( ( C ) =
% 1.04/1.24                   ( k7_subset_1 @
% 1.04/1.24                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 1.04/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.24    (~( ![A:$i]:
% 1.04/1.24        ( ( l1_struct_0 @ A ) =>
% 1.04/1.24          ( ![B:$i]:
% 1.04/1.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24              ( ![C:$i]:
% 1.04/1.24                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24                  ( ( ( ( k2_struct_0 @ A ) =
% 1.04/1.24                        ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) & 
% 1.04/1.24                      ( r1_xboole_0 @ B @ C ) ) =>
% 1.04/1.24                    ( ( C ) =
% 1.04/1.24                      ( k7_subset_1 @
% 1.04/1.24                        ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) )),
% 1.04/1.24    inference('cnf.neg', [status(esa)], [t25_pre_topc])).
% 1.04/1.24  thf('0', plain,
% 1.04/1.24      (((sk_C)
% 1.04/1.24         != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('1', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(redefinition_k9_setfam_1, axiom,
% 1.04/1.24    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 1.04/1.24  thf('2', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('3', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['1', '2'])).
% 1.04/1.24  thf('4', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('5', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('6', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_B @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['4', '5'])).
% 1.04/1.24  thf(dt_k4_subset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.04/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.04/1.24       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.04/1.24  thf('7', plain,
% 1.04/1.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.04/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 1.04/1.24          | (m1_subset_1 @ (k4_subset_1 @ X23 @ X22 @ X24) @ 
% 1.04/1.24             (k1_zfmisc_1 @ X23)))),
% 1.04/1.24      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.04/1.24  thf('8', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('9', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('10', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('11', plain,
% 1.04/1.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X22 @ (k9_setfam_1 @ X23))
% 1.04/1.24          | ~ (m1_subset_1 @ X24 @ (k9_setfam_1 @ X23))
% 1.04/1.24          | (m1_subset_1 @ (k4_subset_1 @ X23 @ X22 @ X24) @ 
% 1.04/1.24             (k9_setfam_1 @ X23)))),
% 1.04/1.24      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.04/1.24  thf('12', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.04/1.24           (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 1.04/1.24          | ~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['6', '11'])).
% 1.04/1.24  thf('13', plain,
% 1.04/1.24      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 1.04/1.24        (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['3', '12'])).
% 1.04/1.24  thf('14', plain,
% 1.04/1.24      (((k2_struct_0 @ sk_A)
% 1.04/1.24         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('15', plain,
% 1.04/1.24      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.04/1.24        (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['13', '14'])).
% 1.04/1.24  thf(redefinition_k7_subset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.24       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.04/1.24  thf('16', plain,
% 1.04/1.24      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.04/1.24          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.04/1.24  thf('17', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('18', plain,
% 1.04/1.24      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X28 @ (k9_setfam_1 @ X29))
% 1.04/1.24          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 1.04/1.24      inference('demod', [status(thm)], ['16', '17'])).
% 1.04/1.24  thf('19', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)
% 1.04/1.24           = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['15', '18'])).
% 1.04/1.24  thf('20', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_C @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['1', '2'])).
% 1.04/1.24  thf('21', plain,
% 1.04/1.24      ((m1_subset_1 @ sk_B @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['4', '5'])).
% 1.04/1.24  thf(redefinition_k4_subset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.04/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.04/1.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.04/1.24  thf('22', plain,
% 1.04/1.24      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 1.04/1.24          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 1.04/1.24          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.04/1.24  thf('23', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('24', plain, (![X31 : $i]: ((k9_setfam_1 @ X31) = (k1_zfmisc_1 @ X31))),
% 1.04/1.24      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.04/1.24  thf('25', plain,
% 1.04/1.24      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X25 @ (k9_setfam_1 @ X26))
% 1.04/1.24          | ~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ X26))
% 1.04/1.24          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 1.04/1.24      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.04/1.24  thf('26', plain,
% 1.04/1.24      (![X0 : $i]:
% 1.04/1.24         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.04/1.24            = (k2_xboole_0 @ sk_B @ X0))
% 1.04/1.24          | ~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['21', '25'])).
% 1.04/1.24  thf('27', plain,
% 1.04/1.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.04/1.24         = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.04/1.24      inference('sup-', [status(thm)], ['20', '26'])).
% 1.04/1.24  thf(commutativity_k2_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.04/1.24  thf('28', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf('29', plain,
% 1.04/1.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.04/1.24         = (k2_xboole_0 @ sk_C @ sk_B))),
% 1.04/1.24      inference('demod', [status(thm)], ['27', '28'])).
% 1.04/1.24  thf('30', plain,
% 1.04/1.24      (((k2_struct_0 @ sk_A)
% 1.04/1.24         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('31', plain, (((k2_struct_0 @ sk_A) = (k2_xboole_0 @ sk_C @ sk_B))),
% 1.04/1.24      inference('sup+', [status(thm)], ['29', '30'])).
% 1.04/1.24  thf(t39_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.04/1.24  thf('32', plain,
% 1.04/1.24      (![X5 : $i, X6 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.04/1.24           = (k2_xboole_0 @ X5 @ X6))),
% 1.04/1.24      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.04/1.24  thf(t40_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.04/1.24  thf('33', plain,
% 1.04/1.24      (![X7 : $i, X8 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 1.04/1.24           = (k4_xboole_0 @ X7 @ X8))),
% 1.04/1.24      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.04/1.24  thf('34', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.04/1.24           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.04/1.24      inference('sup+', [status(thm)], ['32', '33'])).
% 1.04/1.24  thf(t79_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.04/1.24  thf('35', plain,
% 1.04/1.24      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 1.04/1.24      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.04/1.24  thf(symmetry_r1_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.04/1.24  thf('36', plain,
% 1.04/1.24      (![X2 : $i, X3 : $i]:
% 1.04/1.24         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.04/1.24      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.04/1.24  thf('37', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['35', '36'])).
% 1.04/1.24  thf(t88_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( r1_xboole_0 @ A @ B ) =>
% 1.04/1.24       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 1.04/1.24  thf('38', plain,
% 1.04/1.24      (![X20 : $i, X21 : $i]:
% 1.04/1.24         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21) = (X20))
% 1.04/1.24          | ~ (r1_xboole_0 @ X20 @ X21))),
% 1.04/1.24      inference('cnf', [status(esa)], [t88_xboole_1])).
% 1.04/1.24  thf('39', plain,
% 1.04/1.24      (![X7 : $i, X8 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 1.04/1.24           = (k4_xboole_0 @ X7 @ X8))),
% 1.04/1.24      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.04/1.24  thf('40', plain,
% 1.04/1.24      (![X20 : $i, X21 : $i]:
% 1.04/1.24         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 1.04/1.24      inference('demod', [status(thm)], ['38', '39'])).
% 1.04/1.24  thf('41', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]:
% 1.04/1.24         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['37', '40'])).
% 1.04/1.25  thf('42', plain,
% 1.04/1.25      (![X0 : $i, X1 : $i]:
% 1.04/1.25         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.04/1.25           = (X1))),
% 1.04/1.25      inference('demod', [status(thm)], ['34', '41'])).
% 1.04/1.25  thf('43', plain,
% 1.04/1.25      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.04/1.25         = (sk_C))),
% 1.04/1.25      inference('sup+', [status(thm)], ['31', '42'])).
% 1.04/1.25  thf('44', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 1.04/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.25  thf('45', plain,
% 1.04/1.25      (![X20 : $i, X21 : $i]:
% 1.04/1.25         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 1.04/1.25      inference('demod', [status(thm)], ['38', '39'])).
% 1.04/1.25  thf('46', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 1.04/1.25      inference('sup-', [status(thm)], ['44', '45'])).
% 1.04/1.25  thf('47', plain, (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) = (sk_C))),
% 1.04/1.25      inference('demod', [status(thm)], ['43', '46'])).
% 1.04/1.25  thf('48', plain, (((sk_C) != (sk_C))),
% 1.04/1.25      inference('demod', [status(thm)], ['0', '19', '47'])).
% 1.04/1.25  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 1.04/1.25  
% 1.04/1.25  % SZS output end Refutation
% 1.04/1.25  
% 1.04/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
