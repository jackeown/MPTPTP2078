%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FcBeTPMl68

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:04 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 140 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  556 (1189 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
         => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
            & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ( r1_tarski @ X19 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k6_relat_1 @ sk_C ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_D @ X0 )
      | ( r1_tarski @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['43','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FcBeTPMl68
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 837 iterations in 0.299s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.54/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.54/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.76  thf(t30_relset_1, conjecture,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.54/0.76         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.54/0.76           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.54/0.76            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.54/0.76              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.54/0.76        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.54/0.76         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.76         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.54/0.76          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.76  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 0.54/0.76         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.54/0.76      inference('demod', [status(thm)], ['1', '4'])).
% 0.54/0.76  thf(t21_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( r1_tarski @
% 0.54/0.76         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      (![X19 : $i]:
% 0.54/0.76         ((r1_tarski @ X19 @ 
% 0.54/0.76           (k2_zfmisc_1 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 0.54/0.76          | ~ (v1_relat_1 @ X19))),
% 0.54/0.76      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.54/0.76  thf(t12_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.54/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ((k2_xboole_0 @ X0 @ 
% 0.54/0.76              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.54/0.76              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.76  thf(d10_xboole_0, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.76  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.54/0.76      inference('simplify', [status(thm)], ['9'])).
% 0.54/0.76  thf(t11_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.76         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.54/0.76      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.76  thf('13', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.54/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.76  thf('15', plain, (((k2_xboole_0 @ (k6_relat_1 @ sk_C) @ sk_D) = (sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.76         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.54/0.76      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (r1_tarski @ sk_D @ X0) | (r1_tarski @ (k6_relat_1 @ sk_C) @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (r1_tarski @ (k6_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_D @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['12', '17'])).
% 0.54/0.76  thf(t3_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (![X8 : $i, X10 : $i]:
% 0.54/0.76         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.54/0.76          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      (((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.54/0.76         (k1_zfmisc_1 @ 
% 0.54/0.76          (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))
% 0.54/0.76        | ~ (v1_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup+', [status(thm)], ['8', '20'])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc2_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      (![X11 : $i, X12 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.54/0.76          | (v1_relat_1 @ X11)
% 0.54/0.76          | ~ (v1_relat_1 @ X12))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.54/0.76  thf(fc6_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.76  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('27', plain,
% 0.54/0.76      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.54/0.76        (k1_zfmisc_1 @ 
% 0.54/0.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.54/0.76      inference('demod', [status(thm)], ['21', '26'])).
% 0.54/0.76  thf(cc2_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.54/0.76         ((v4_relat_1 @ X24 @ X25)
% 0.54/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.76  thf('29', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.76  thf(d18_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ B ) =>
% 0.54/0.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      (![X13 : $i, X14 : $i]:
% 0.54/0.76         (~ (v4_relat_1 @ X13 @ X14)
% 0.54/0.76          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.54/0.76          | ~ (v1_relat_1 @ X13))),
% 0.54/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.54/0.76        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.76  thf(fc4_funct_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.54/0.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.54/0.76  thf('32', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.54/0.76  thf(t71_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.54/0.76       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.54/0.76  thf('33', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.54/0.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.76  thf('34', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.54/0.76      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.76         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.54/0.76          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.54/0.76         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.54/0.76         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.76  thf('40', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['34', '39'])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.54/0.76       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.54/0.76      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.54/0.76  thf('43', plain, (~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.54/0.76      inference('simpl_trail', [status(thm)], ['5', '42'])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.54/0.76        (k1_zfmisc_1 @ 
% 0.54/0.76         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.54/0.76      inference('demod', [status(thm)], ['21', '26'])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.54/0.76         ((v5_relat_1 @ X24 @ X26)
% 0.54/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.76  thf('46', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.76  thf(d19_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ B ) =>
% 0.54/0.76       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X15 : $i, X16 : $i]:
% 0.54/0.76         (~ (v5_relat_1 @ X15 @ X16)
% 0.54/0.76          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.54/0.76          | ~ (v1_relat_1 @ X15))),
% 0.54/0.76      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.54/0.76        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.76  thf('49', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.54/0.76  thf('50', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.54/0.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.76  thf('51', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.54/0.76      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.54/0.76  thf('52', plain, ($false), inference('demod', [status(thm)], ['43', '51'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
