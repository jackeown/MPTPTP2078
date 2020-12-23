%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hYVRk4nEfa

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:32 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 451 expanded)
%              Number of leaves         :   20 ( 136 expanded)
%              Depth                    :   19
%              Number of atoms          :  713 (10736 expanded)
%              Number of equality atoms :   18 ( 248 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X15 @ X12 )
      | ( r2_hidden @ ( sk_E @ X12 @ X15 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( m1_subset_1 @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X16 )
        = ( k1_funct_1 @ sk_D @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
      = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X15 @ X12 )
      | ( ( k1_funct_1 @ X15 @ ( sk_E @ X12 @ X15 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_E @ X12 @ X15 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['3','34'])).

thf('36',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ~ ( r2_relset_1 @ sk_C @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('45',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['3','34'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_C = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_C = sk_D ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( r2_relset_1 @ X9 @ X10 @ X8 @ X11 )
      | ( X8 != X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X9 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['35','38'])).

thf('55',plain,(
    r2_relset_1 @ sk_C @ sk_B @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['40','49','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hYVRk4nEfa
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 172 iterations in 0.137s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.59  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(t113_funct_2, conjecture,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59       ( ![D:$i]:
% 0.36/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59           ( ( ![E:$i]:
% 0.36/0.59               ( ( m1_subset_1 @ E @ A ) =>
% 0.36/0.59                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.36/0.59             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59          ( ![D:$i]:
% 0.36/0.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59              ( ( ![E:$i]:
% 0.36/0.59                  ( ( m1_subset_1 @ E @ A ) =>
% 0.36/0.59                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.36/0.59                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 0.36/0.59  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(cc3_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.59       ( ![C:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X5)
% 0.36/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X7)))
% 0.36/0.59          | (v1_xboole_0 @ X6))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.36/0.59  thf('3', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t18_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59       ( ![D:$i]:
% 0.36/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59           ( ( ![E:$i]:
% 0.36/0.59               ( ( r2_hidden @ E @ A ) =>
% 0.36/0.59                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.36/0.59             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X12)
% 0.36/0.59          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.36/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.36/0.59          | (r2_relset_1 @ X13 @ X14 @ X15 @ X12)
% 0.36/0.59          | (r2_hidden @ (sk_E @ X12 @ X15 @ X13) @ X13)
% 0.36/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.36/0.59          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.36/0.59          | ~ (v1_funct_1 @ X15))),
% 0.36/0.59      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.36/0.59          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.36/0.59          | (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 0.36/0.59          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.59  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.36/0.59          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.36/0.59          | (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D))),
% 0.36/0.59      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.36/0.59        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.59        | ~ (v1_funct_1 @ sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['5', '11'])).
% 0.36/0.59  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.36/0.59        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.36/0.59  thf('16', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('17', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['15', '16'])).
% 0.36/0.59  thf(d2_subset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X2 @ X3)
% 0.36/0.59          | (m1_subset_1 @ X2 @ X3)
% 0.36/0.59          | (v1_xboole_0 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_A)
% 0.36/0.59        | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X16 : $i]:
% 0.36/0.59         (((k1_funct_1 @ sk_C @ X16) = (k1_funct_1 @ sk_D @ X16))
% 0.36/0.59          | ~ (m1_subset_1 @ X16 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_A)
% 0.36/0.59        | ((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.36/0.59            = (k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X12)
% 0.36/0.59          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.36/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.36/0.59          | (r2_relset_1 @ X13 @ X14 @ X15 @ X12)
% 0.36/0.59          | ((k1_funct_1 @ X15 @ (sk_E @ X12 @ X15 @ X13))
% 0.36/0.59              != (k1_funct_1 @ X12 @ (sk_E @ X12 @ X15 @ X13)))
% 0.36/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.36/0.59          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.36/0.59          | ~ (v1_funct_1 @ X15))),
% 0.36/0.59      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.36/0.59            != (k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A)))
% 0.36/0.59          | (v1_xboole_0 @ sk_A)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.36/0.59          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.36/0.59          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.59  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.36/0.59            != (k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A)))
% 0.36/0.59          | (v1_xboole_0 @ sk_A)
% 0.36/0.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.36/0.59          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.36/0.59          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.36/0.59          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.36/0.59          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.36/0.59          | (v1_xboole_0 @ sk_A))),
% 0.36/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_A)
% 0.36/0.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.59        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.36/0.59        | (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.36/0.59        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '27'])).
% 0.36/0.59  thf('29', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_A) | (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.36/0.59      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.36/0.59  thf('33', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('34', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['32', '33'])).
% 0.36/0.59  thf('35', plain, ((v1_xboole_0 @ sk_C)),
% 0.36/0.59      inference('demod', [status(thm)], ['3', '34'])).
% 0.36/0.59  thf('36', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['32', '33'])).
% 0.36/0.59  thf(t8_boole, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t8_boole])).
% 0.36/0.59  thf('38', plain, (![X0 : $i]: (((sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('39', plain, (((sk_A) = (sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['35', '38'])).
% 0.36/0.59  thf('40', plain, (~ (r2_relset_1 @ sk_C @ sk_B @ sk_C @ sk_D)),
% 0.36/0.59      inference('demod', [status(thm)], ['0', '39'])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X5)
% 0.36/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X7)))
% 0.36/0.59          | (v1_xboole_0 @ X6))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.36/0.59  thf('43', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.59  thf('44', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['32', '33'])).
% 0.36/0.59  thf('45', plain, ((v1_xboole_0 @ sk_D)),
% 0.36/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.59  thf('46', plain, ((v1_xboole_0 @ sk_C)),
% 0.36/0.59      inference('demod', [status(thm)], ['3', '34'])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t8_boole])).
% 0.36/0.59  thf('48', plain, (![X0 : $i]: (((sk_C) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf('49', plain, (((sk_C) = (sk_D))),
% 0.36/0.59      inference('sup-', [status(thm)], ['45', '48'])).
% 0.36/0.59  thf('50', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.59  thf('51', plain,
% 0.36/0.59      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.36/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.36/0.59          | (r2_relset_1 @ X9 @ X10 @ X8 @ X11)
% 0.36/0.59          | ((X8) != (X11)))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.59  thf('52', plain,
% 0.36/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.59         ((r2_relset_1 @ X9 @ X10 @ X11 @ X11)
% 0.36/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.59  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.36/0.59      inference('sup-', [status(thm)], ['50', '52'])).
% 0.36/0.59  thf('54', plain, (((sk_A) = (sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['35', '38'])).
% 0.36/0.59  thf('55', plain, ((r2_relset_1 @ sk_C @ sk_B @ sk_C @ sk_C)),
% 0.36/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.59  thf('56', plain, ($false),
% 0.36/0.59      inference('demod', [status(thm)], ['40', '49', '55'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
