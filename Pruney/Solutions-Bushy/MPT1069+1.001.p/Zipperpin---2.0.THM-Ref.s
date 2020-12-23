%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1069+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1vpW0lFADP

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 217 expanded)
%              Number of leaves         :   38 (  81 expanded)
%              Depth                    :   22
%              Number of atoms          : 1151 (4454 expanded)
%              Number of equality atoms :   68 ( 200 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ ( k2_relset_1 @ X31 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v5_relat_1 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('15',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( ( k7_partfun1 @ X8 @ X7 @ X6 )
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ X13 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X13 @ X14 @ X17 @ X12 @ X16 ) @ X15 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X12 @ X15 ) ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X13 @ X14 @ X12 ) @ ( k1_relset_1 @ X14 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('49',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','49','50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','54'])).

thf('56',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['35','55'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('60',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('66',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('72',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('73',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('74',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82','83'])).


%------------------------------------------------------------------------------
