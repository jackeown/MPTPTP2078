%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mi9hIxSOob

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  611 (1888 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(t47_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                    <=> ? [E: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                          & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relset_1])).

thf('0',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X26 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X26 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k8_relset_1 @ X23 @ X24 @ X25 @ X24 )
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('10',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('15',plain,
    ( ( k10_relat_1 @ sk_C_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k10_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_D_2 @ X12 @ X10 @ X11 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X26 ) @ sk_C_1 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X26 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X26 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('26',plain,
    ( ( k10_relat_1 @ sk_C_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k10_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D_2 @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ X26 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k1_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_3 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mi9hIxSOob
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 85 iterations in 0.061s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.20/0.52  thf(t47_relset_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.52                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.20/0.52                     ( ?[E:$i]:
% 0.20/0.52                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.20/0.52                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.52                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.20/0.52                        ( ?[E:$i]:
% 0.20/0.52                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.20/0.52                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X26 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X26) @ sk_C_1)
% 0.20/0.52          | ~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((![X26 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X26) @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)
% 0.20/0.52        | (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t38_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.52         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (((k8_relset_1 @ X23 @ X24 @ X25 @ X24)
% 0.20/0.52            = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.20/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_B)
% 0.20/0.52         = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.52          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.52           = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('15', plain, (((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.20/0.52  thf(t166_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.52         ( ?[D:$i]:
% 0.20/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.52             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.52             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ (k10_relat_1 @ X12 @ X10))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X11 @ (sk_D_2 @ X12 @ X10 @ X11)) @ X12)
% 0.20/0.52          | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.52          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ sk_C_1 @ sk_B @ X0)) @ 
% 0.20/0.52             sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( v1_relat_1 @ C ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         ((v1_relat_1 @ X13)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.52  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ sk_C_1 @ sk_B @ X0)) @ 
% 0.20/0.52             sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ sk_D_3 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3)) @ sk_C_1))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((![X26 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X26) @ sk_C_1)))
% 0.20/0.52         <= ((![X26 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X26) @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.20/0.52             (![X26 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X26) @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.52  thf('26', plain, (((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ (k10_relat_1 @ X12 @ X10))
% 0.20/0.52          | (r2_hidden @ (sk_D_2 @ X12 @ X10 @ X11) @ X10)
% 0.20/0.52          | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.52          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.52          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.52          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.52  thf(t1_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (~
% 0.20/0.52       (![X26 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_3 @ X26) @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['24', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)) | 
% 0.20/0.52       ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf(d4_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4)
% 0.20/0.52          | (r2_hidden @ X2 @ X5)
% 0.20/0.52          | ((X5) != (k1_relat_1 @ X4)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         ((r2_hidden @ X2 @ (k1_relat_1 @ X4))
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.20/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_D_3 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.52         <= (~ ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (~ ((r2_hidden @ (k4_tarski @ sk_D_3 @ sk_E) @ sk_C_1)) | 
% 0.20/0.52       ((r2_hidden @ sk_D_3 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.20/0.52  thf('44', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '34', '35', '43'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
