%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W60wzAcCvA

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 183 expanded)
%              Number of leaves         :   39 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          : 1023 (3894 expanded)
%              Number of equality atoms :   56 ( 171 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X32 @ X29 ) @ ( k2_relset_1 @ X30 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k7_partfun1 @ X22 @ X21 @ X20 )
        = ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A_1 ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['28','33','34'])).

thf('36',plain,
    ( ( ( k7_partfun1 @ sk_A_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','35'])).

thf('37',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ X24 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X24 @ X25 @ X28 @ X23 @ X27 ) @ X26 )
        = ( k1_funct_1 @ X27 @ ( k1_funct_1 @ X23 @ X26 ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X24 @ X25 @ X23 ) @ ( k1_relset_1 @ X25 @ X28 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A_1 ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('52',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('54',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','54','55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['37','60'])).

thf('62',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','61'])).

thf('63',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['62'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('64',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('68',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('69',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('70',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W60wzAcCvA
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 71 iterations in 0.041s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(t186_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50           ( ![E:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.50               ( ![F:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.50                   ( ( r1_tarski @
% 0.21/0.50                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.50                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.50                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.50                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.50          ( ![D:$i]:
% 0.21/0.50            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50              ( ![E:$i]:
% 0.21/0.50                ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                    ( m1_subset_1 @
% 0.21/0.50                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.50                  ( ![F:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.50                      ( ( r1_tarski @
% 0.21/0.50                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.50                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.50                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50                          ( ( k1_funct_1 @
% 0.21/0.50                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.50                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.21/0.50  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((v5_relat_1 @ X11 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t2_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         ((r2_hidden @ X5 @ X6)
% 0.21/0.50          | (v1_xboole_0 @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.50  thf('6', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t6_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X29 @ X30)
% 0.21/0.50          | ((X31) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_funct_1 @ X32)
% 0.21/0.50          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.21/0.50          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.50          | (r2_hidden @ (k1_funct_1 @ X32 @ X29) @ 
% 0.21/0.50             (k2_relset_1 @ X30 @ X31 @ X32)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.50           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.50          | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.21/0.50          | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((v1_xboole_0 @ sk_B)
% 0.21/0.50        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.50        (k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.50        | (v1_xboole_0 @ sk_B)
% 0.21/0.50        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '25'])).
% 0.21/0.50  thf(d8_partfun1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.50           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.21/0.50          | ((k7_partfun1 @ X22 @ X21 @ X20) = (k1_funct_1 @ X21 @ X20))
% 0.21/0.50          | ~ (v1_funct_1 @ X21)
% 0.21/0.50          | ~ (v5_relat_1 @ X21 @ X22)
% 0.21/0.50          | ~ (v1_relat_1 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ sk_B)
% 0.21/0.50          | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ sk_E)
% 0.21/0.50          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.50              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.50          | (v1_relat_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A_1)) | (v1_relat_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('33', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ sk_B)
% 0.21/0.50          | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.21/0.50          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.50              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((k7_partfun1 @ sk_A_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.50          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.50        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50        | (v1_xboole_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E) @ 
% 0.21/0.50         sk_F) != (k7_partfun1 @ sk_A_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t185_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50           ( ![E:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.50               ( ![F:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.50                   ( ( r1_tarski @
% 0.21/0.50                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.50                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.50                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.50                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X23)
% 0.21/0.50          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ X24)
% 0.21/0.50          | ((k1_funct_1 @ (k8_funct_2 @ X24 @ X25 @ X28 @ X23 @ X27) @ X26)
% 0.21/0.50              = (k1_funct_1 @ X27 @ (k1_funct_1 @ X23 @ X26)))
% 0.21/0.50          | ((X24) = (k1_xboole_0))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relset_1 @ X24 @ X25 @ X23) @ 
% 0.21/0.50               (k1_relset_1 @ X25 @ X28 @ X27))
% 0.21/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X28)))
% 0.21/0.50          | ~ (v1_funct_1 @ X27)
% 0.21/0.50          | (v1_xboole_0 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ sk_C_1)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.50               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.21/0.50          | ((sk_B) = (k1_xboole_0))
% 0.21/0.50          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.50              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ sk_C_1)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.21/0.50               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.21/0.50          | ((sk_B) = (k1_xboole_0))
% 0.21/0.50          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.50              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.21/0.50  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ sk_C_1)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.21/0.50               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.21/0.50          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.50              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.50          | ((k1_funct_1 @ 
% 0.21/0.50              (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E) @ X0)
% 0.21/0.50              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.50          | ~ (m1_subset_1 @ sk_E @ 
% 0.21/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A_1)))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50          | (v1_xboole_0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.50        (k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_C_1 @ sk_A_1 @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('54', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.50          | ((k1_funct_1 @ 
% 0.21/0.50              (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E) @ X0)
% 0.21/0.50              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.50          | (v1_xboole_0 @ sk_C_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '54', '55', '56'])).
% 0.21/0.50  thf('58', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E) @ 
% 0.21/0.50            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A_1 @ sk_D @ sk_E) @ 
% 0.21/0.50         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.50         != (k7_partfun1 @ sk_A_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.50          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.50        | (v1_xboole_0 @ sk_B)
% 0.21/0.50        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '61'])).
% 0.21/0.50  thf('63', plain, ((((sk_C_1) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B))),
% 0.21/0.50      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.50  thf(l13_xboole_0, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.50  thf('65', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.50  thf('66', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.21/0.50  thf('68', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.50  thf('69', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.50  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['68', '71'])).
% 0.21/0.50  thf('73', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '67', '72'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
