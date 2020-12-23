%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MNph0D3XRA

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 110 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  651 (1104 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t63_setfam_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v3_setfam_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v3_setfam_1 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
             => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v3_setfam_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v3_setfam_1 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
               => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_setfam_1 @ X33 @ X32 )
      | ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v3_setfam_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('11',plain,
    ( ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k4_subset_1 @ X28 @ X27 @ X29 )
        = ( k3_tarski @ ( k2_tarski @ X27 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ ( k6_subset_1 @ X12 @ X11 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( zip_tseitin_0 @ X10 @ X9 @ X8 )
      | ( zip_tseitin_1 @ X10 @ X9 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( zip_tseitin_0 @ X10 @ X9 @ X8 )
      | ( zip_tseitin_1 @ X10 @ X9 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( zip_tseitin_1 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) @ X1 )
      | ( zip_tseitin_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X13 @ X14 ) @ X14 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( zip_tseitin_1 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) @ X1 )
      | ( zip_tseitin_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k6_subset_1 @ sk_C @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k6_subset_1 @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( zip_tseitin_1 @ X5 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k6_subset_1 @ sk_C @ sk_B ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v3_setfam_1 @ X33 @ X32 )
      | ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    zip_tseitin_0 @ sk_A @ ( k6_subset_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k6_subset_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['4','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MNph0D3XRA
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:28:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 124 iterations in 0.069s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(t63_setfam_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.20/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.20/0.53                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.20/0.53               ( v3_setfam_1 @
% 0.20/0.53                 ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.20/0.53                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.20/0.53                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.20/0.53                  ( v3_setfam_1 @
% 0.20/0.53                    ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t63_setfam_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d13_setfam_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i]:
% 0.20/0.53         (~ (v3_setfam_1 @ X33 @ X32)
% 0.20/0.53          | ~ (r2_hidden @ X32 @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X32))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ sk_C) | ~ (v3_setfam_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf('3', plain, ((v3_setfam_1 @ sk_C @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k4_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.20/0.53          | (m1_subset_1 @ (k4_subset_1 @ X20 @ X19 @ X21) @ 
% 0.20/0.53             (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i]:
% 0.20/0.53         ((r2_hidden @ X32 @ X33)
% 0.20/0.53          | (v3_setfam_1 @ X33 @ X32)
% 0.20/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X32))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.53         sk_A)
% 0.20/0.53        | (r2_hidden @ sk_A @ 
% 0.20/0.53           (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (~ (v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.53          sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((r2_hidden @ sk_A @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 0.20/0.53          | ((k4_subset_1 @ X28 @ X27 @ X29) = (k2_xboole_0 @ X27 @ X29)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.53  thf(l51_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28))
% 0.20/0.53          | ((k4_subset_1 @ X28 @ X27 @ X29)
% 0.20/0.53              = (k3_tarski @ (k2_tarski @ X27 @ X29))))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0)
% 0.20/0.53            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.53         = (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((r2_hidden @ sk_A @ (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '20'])).
% 0.20/0.53  thf(t39_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.20/0.53           = (k2_xboole_0 @ X11 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.53  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i]:
% 0.20/0.53         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X11 @ (k6_subset_1 @ X12 @ X11)))
% 0.20/0.53           = (k3_tarski @ (k2_tarski @ X11 @ X12)))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.53  thf(t5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.20/0.53          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.53          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_2, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.53       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_4, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.53       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_5, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.20/0.53          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.20/0.53          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.53          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.53          | (zip_tseitin_0 @ X10 @ X9 @ X8)
% 0.20/0.53          | (zip_tseitin_1 @ X10 @ X9 @ X8)
% 0.20/0.53          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.53          | (zip_tseitin_0 @ X10 @ X9 @ X8)
% 0.20/0.53          | (zip_tseitin_1 @ X10 @ X9 @ X8)
% 0.20/0.53          | ~ (r2_hidden @ X10 @ (k3_tarski @ (k2_tarski @ X8 @ X9))))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 0.20/0.53          | (zip_tseitin_1 @ X2 @ (k6_subset_1 @ X0 @ X1) @ X1)
% 0.20/0.53          | (zip_tseitin_0 @ X2 @ (k6_subset_1 @ X0 @ X1) @ X1)
% 0.20/0.53          | ~ (r1_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.53  thf(t79_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.20/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i]:
% 0.20/0.53         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X13 @ X14) @ X14)),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 0.20/0.53          | (zip_tseitin_1 @ X2 @ (k6_subset_1 @ X0 @ X1) @ X1)
% 0.20/0.53          | (zip_tseitin_0 @ X2 @ (k6_subset_1 @ X0 @ X1) @ X1))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((zip_tseitin_0 @ sk_A @ (k6_subset_1 @ sk_C @ sk_B) @ sk_B)
% 0.20/0.53        | (zip_tseitin_1 @ sk_A @ (k6_subset_1 @ sk_C @ sk_B) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((r2_hidden @ X5 @ X6) | ~ (zip_tseitin_1 @ X5 @ X7 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((zip_tseitin_0 @ sk_A @ (k6_subset_1 @ sk_C @ sk_B) @ sk_B)
% 0.20/0.53        | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i]:
% 0.20/0.53         (~ (v3_setfam_1 @ X33 @ X32)
% 0.20/0.53          | ~ (r2_hidden @ X32 @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X32))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((zip_tseitin_0 @ sk_A @ (k6_subset_1 @ sk_C @ sk_B) @ sk_B)),
% 0.20/0.53      inference('clc', [status(thm)], ['39', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((r2_hidden @ X2 @ X3) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.53  thf('47', plain, ((r2_hidden @ sk_A @ (k6_subset_1 @ sk_C @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf(dt_k6_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k6_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.20/0.53  thf(l3_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X24 @ X25)
% 0.20/0.53          | (r2_hidden @ X24 @ X26)
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '50'])).
% 0.20/0.53  thf('52', plain, ($false), inference('demod', [status(thm)], ['4', '51'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
