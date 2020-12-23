%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PaUBWygEXS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 105 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  625 (1703 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_funct_1 @ X10 @ ( sk_E @ X10 @ X11 @ X12 ) )
        = X11 )
      | ~ ( r2_hidden @ X11 @ ( k2_relset_1 @ X12 @ X13 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t17_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ X0 @ sk_B ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ X0 @ sk_B ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) )
        = ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_E @ X10 @ X11 @ X12 ) @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k2_relset_1 @ X12 @ X13 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t17_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ X7 )
      | ( ( k3_funct_2 @ X7 @ X8 @ X6 @ X9 )
        = ( k1_funct_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) )
        = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X14 ) @ sk_A )
      | ~ ( m1_subset_1 @ X14 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_A )
      | ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ sk_A )
    | ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PaUBWygEXS
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:41:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 40 iterations in 0.029s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.49  thf(t191_funct_2, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.49           ( ![D:$i]:
% 0.22/0.49             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.49                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.49               ( ( ![E:$i]:
% 0.22/0.49                   ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.49                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.22/0.49                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.49          ( ![C:$i]:
% 0.22/0.49            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.49              ( ![D:$i]:
% 0.22/0.49                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.49                    ( m1_subset_1 @
% 0.22/0.49                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.49                  ( ( ![E:$i]:
% 0.22/0.49                      ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.49                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.22/0.49                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t17_funct_2, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.49       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.49            ( ![E:$i]:
% 0.22/0.49              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         (((k1_funct_1 @ X10 @ (sk_E @ X10 @ X11 @ X12)) = (X11))
% 0.22/0.49          | ~ (r2_hidden @ X11 @ (k2_relset_1 @ X12 @ X13 @ X10))
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.49          | ~ (v1_funct_2 @ X10 @ X12 @ X13)
% 0.22/0.49          | ~ (v1_funct_1 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t17_funct_2])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_funct_1 @ sk_D)
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.22/0.49          | ((k1_funct_1 @ sk_D @ (sk_E @ sk_D @ X0 @ sk_B)) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.22/0.49          | ((k1_funct_1 @ sk_D @ (sk_E @ sk_D @ X0 @ sk_B)) = (X0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | ((k1_funct_1 @ sk_D @ 
% 0.22/0.49              (sk_E @ sk_D @ 
% 0.22/0.49               (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B))
% 0.22/0.49              = (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         ((r2_hidden @ (sk_E @ X10 @ X11 @ X12) @ X12)
% 0.22/0.49          | ~ (r2_hidden @ X11 @ (k2_relset_1 @ X12 @ X13 @ X10))
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.49          | ~ (v1_funct_2 @ X10 @ X12 @ X13)
% 0.22/0.49          | ~ (v1_funct_1 @ X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t17_funct_2])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_funct_1 @ sk_D)
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.22/0.49          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.22/0.49          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_B) @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.22/0.49          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_B) @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (r2_hidden @ 
% 0.22/0.49             (sk_E @ sk_D @ 
% 0.22/0.49              (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B) @ 
% 0.22/0.49             sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '15'])).
% 0.22/0.49  thf(t1_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (m1_subset_1 @ 
% 0.22/0.49             (sk_E @ sk_D @ 
% 0.22/0.49              (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B) @ 
% 0.22/0.49             sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k3_funct_2, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.22/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.22/0.49          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 0.22/0.49          | ~ (v1_funct_1 @ X6)
% 0.22/0.49          | (v1_xboole_0 @ X7)
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ X7)
% 0.22/0.49          | ((k3_funct_2 @ X7 @ X8 @ X6 @ X9) = (k1_funct_1 @ X6 @ X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.49          | (v1_xboole_0 @ sk_B)
% 0.22/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.49          | (v1_xboole_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.22/0.49  thf('25', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.49          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X0)
% 0.22/0.49              = (k1_funct_1 @ sk_D @ X0)))),
% 0.22/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ 
% 0.22/0.49              (sk_E @ sk_D @ 
% 0.22/0.49               (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B))
% 0.22/0.49              = (k1_funct_1 @ sk_D @ 
% 0.22/0.49                 (sk_E @ sk_D @ 
% 0.22/0.49                  (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (m1_subset_1 @ 
% 0.22/0.49             (sk_E @ sk_D @ 
% 0.22/0.49              (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B) @ 
% 0.22/0.49             sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X14 : $i]:
% 0.22/0.49         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ X14) @ sk_A)
% 0.22/0.49          | ~ (m1_subset_1 @ X14 @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (r2_hidden @ 
% 0.22/0.49             (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D @ 
% 0.22/0.49              (sk_E @ sk_D @ 
% 0.22/0.49               (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B)) @ 
% 0.22/0.49             sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ 
% 0.22/0.49           (k1_funct_1 @ sk_D @ 
% 0.22/0.49            (sk_E @ sk_D @ 
% 0.22/0.49             (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B)) @ 
% 0.22/0.49           sk_A)
% 0.22/0.49          | (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['27', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (r2_hidden @ 
% 0.22/0.49             (k1_funct_1 @ sk_D @ 
% 0.22/0.49              (sk_E @ sk_D @ 
% 0.22/0.49               (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ sk_B)) @ 
% 0.22/0.49             sk_A))),
% 0.22/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ 
% 0.22/0.49           sk_A)
% 0.22/0.49          | (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['8', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.22/0.49          | (r2_hidden @ (sk_C @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)) @ 
% 0.22/0.49             sk_A))),
% 0.22/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ sk_A)
% 0.22/0.49        | (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain, ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ sk_A)),
% 0.22/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.49  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
