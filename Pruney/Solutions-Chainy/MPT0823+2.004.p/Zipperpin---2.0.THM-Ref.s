%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GOSoisU3kH

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:00 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  655 (1447 expanded)
%              Number of equality atoms :   51 ( 101 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t24_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_relset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_relset_1 @ X15 @ X16 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('3',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('18',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('19',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('38',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['16','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('42',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GOSoisU3kH
% 0.16/0.39  % Computer   : n010.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 11:27:15 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 33 iterations in 0.020s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.49  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.49  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(t37_relat_1, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ A ) =>
% 0.24/0.49       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.24/0.49         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      (![X4 : $i]:
% 0.24/0.49         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.24/0.49          | ~ (v1_relat_1 @ X4))),
% 0.24/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.24/0.49  thf(t24_relset_1, conjecture,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.24/0.49           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.24/0.49         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.24/0.49           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49          ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.24/0.49              ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.24/0.49            ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.24/0.49              ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t24_relset_1])).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(redefinition_k3_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.49         (((k3_relset_1 @ X15 @ X16 @ X14) = (k4_relat_1 @ X14))
% 0.24/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.24/0.49  thf('3', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.49  thf('4', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(dt_k3_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( m1_subset_1 @
% 0.24/0.49         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.24/0.49         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.49         ((m1_subset_1 @ (k3_relset_1 @ X5 @ X6 @ X7) @ 
% 0.24/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.24/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.24/0.49  thf('7', plain,
% 0.24/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.24/0.49         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.24/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49         = (k2_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.49  thf('9', plain,
% 0.24/0.49      ((((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49        | ((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('10', plain,
% 0.24/0.49      ((((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.49         <= (~
% 0.24/0.49             (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.49      inference('split', [status(esa)], ['9'])).
% 0.24/0.49  thf('11', plain,
% 0.24/0.49      ((((k2_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.49         <= (~
% 0.24/0.49             (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['8', '10'])).
% 0.24/0.49  thf('12', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.24/0.49  thf('13', plain,
% 0.24/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.49         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.24/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.49  thf('14', plain,
% 0.24/0.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.49  thf('15', plain,
% 0.24/0.49      ((((k2_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.49          != (k1_relat_1 @ sk_C)))
% 0.24/0.49         <= (~
% 0.24/0.49             (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('demod', [status(thm)], ['11', '14'])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (![X4 : $i]:
% 0.24/0.50         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.24/0.50          | ~ (v1_relat_1 @ X4))),
% 0.24/0.50      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.24/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf('19', plain,
% 0.24/0.50      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.50  thf('20', plain,
% 0.24/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.50         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.24/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.24/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.50  thf('21', plain,
% 0.24/0.50      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.50  thf('22', plain,
% 0.24/0.50      ((((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('split', [status(esa)], ['9'])).
% 0.24/0.50  thf('23', plain,
% 0.24/0.50      ((((k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.50  thf('24', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('25', plain,
% 0.24/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.24/0.50         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.24/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.24/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.50  thf('26', plain,
% 0.24/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.24/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.50  thf('27', plain,
% 0.24/0.50      ((((k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          != (k2_relat_1 @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('demod', [status(thm)], ['23', '26'])).
% 0.24/0.50  thf('28', plain,
% 0.24/0.50      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['18', '27'])).
% 0.24/0.50  thf('29', plain,
% 0.24/0.50      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['17', '28'])).
% 0.24/0.50  thf('30', plain,
% 0.24/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(cc2_relat_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ A ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.50  thf('31', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.24/0.50          | (v1_relat_1 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.50  thf('32', plain,
% 0.24/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.24/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.50  thf(fc6_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.50  thf('33', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.50  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.24/0.50  thf('35', plain,
% 0.24/0.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.24/0.50         <= (~
% 0.24/0.50             (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.24/0.50      inference('demod', [status(thm)], ['29', '34'])).
% 0.24/0.50  thf('36', plain,
% 0.24/0.50      ((((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['35'])).
% 0.24/0.50  thf('37', plain,
% 0.24/0.50      (~
% 0.24/0.50       (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.24/0.50       ~
% 0.24/0.50       (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.50      inference('split', [status(esa)], ['9'])).
% 0.24/0.50  thf('38', plain,
% 0.24/0.50      (~
% 0.24/0.50       (((k2_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.24/0.50          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.24/0.50      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.24/0.50  thf('39', plain,
% 0.24/0.50      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.24/0.50      inference('simpl_trail', [status(thm)], ['16', '38'])).
% 0.24/0.50  thf('40', plain,
% 0.24/0.50      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '39'])).
% 0.24/0.50  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.24/0.50  thf('42', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.50  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
