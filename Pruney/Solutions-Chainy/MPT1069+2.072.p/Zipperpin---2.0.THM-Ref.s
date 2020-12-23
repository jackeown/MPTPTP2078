%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2aBrBE415m

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:11 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 207 expanded)
%              Number of leaves         :   38 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          : 1153 (4430 expanded)
%              Number of equality atoms :   66 ( 194 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X34 @ X31 ) @ ( k2_relset_1 @ X32 @ X33 @ X34 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k7_partfun1 @ X24 @ X23 @ X22 )
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['28','33','34'])).

thf('36',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ X26 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X26 @ X27 @ X30 @ X25 @ X29 ) @ X28 )
        = ( k1_funct_1 @ X29 @ ( k1_funct_1 @ X25 @ X28 ) ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X26 @ X27 @ X25 ) @ ( k1_relset_1 @ X27 @ X30 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('42',plain,(
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
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('51',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','51','52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['38','56'])).

thf('58',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['37','57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('68',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2aBrBE415m
% 0.17/0.37  % Computer   : n011.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 15:31:12 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 77 iterations in 0.043s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.52  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.24/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.24/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.24/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.52  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.24/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(t186_funct_2, conjecture,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.52       ( ![D:$i]:
% 0.24/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.24/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.24/0.52           ( ![E:$i]:
% 0.24/0.52             ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.52                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.24/0.52               ( ![F:$i]:
% 0.24/0.52                 ( ( m1_subset_1 @ F @ B ) =>
% 0.24/0.52                   ( ( r1_tarski @
% 0.24/0.52                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.24/0.52                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.24/0.52                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.52                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.24/0.52                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.52        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.52          ( ![D:$i]:
% 0.24/0.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.24/0.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.24/0.52              ( ![E:$i]:
% 0.24/0.52                ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.52                    ( m1_subset_1 @
% 0.24/0.52                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.24/0.52                  ( ![F:$i]:
% 0.24/0.52                    ( ( m1_subset_1 @ F @ B ) =>
% 0.24/0.52                      ( ( r1_tarski @
% 0.24/0.52                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.24/0.52                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.24/0.52                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.52                          ( ( k1_funct_1 @
% 0.24/0.52                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.24/0.52                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.24/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t2_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (![X1 : $i, X2 : $i]:
% 0.24/0.52         ((r2_hidden @ X1 @ X2)
% 0.24/0.52          | (v1_xboole_0 @ X2)
% 0.24/0.52          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.52  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.24/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t6_funct_2, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.24/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X31 @ X32)
% 0.24/0.52          | ((X33) = (k1_xboole_0))
% 0.24/0.52          | ~ (v1_funct_1 @ X34)
% 0.24/0.52          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.24/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.24/0.52          | (r2_hidden @ (k1_funct_1 @ X34 @ X31) @ 
% 0.24/0.52             (k2_relset_1 @ X32 @ X33 @ X34)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.24/0.52           (k2_relset_1 @ sk_B @ sk_C @ sk_D))
% 0.24/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.24/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.24/0.52          | ((sk_C) = (k1_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.24/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.52  thf('7', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.24/0.52           (k2_relset_1 @ sk_B @ sk_C @ sk_D))
% 0.24/0.52          | ((sk_C) = (k1_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      (((v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.24/0.52           (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['3', '9'])).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(cc2_relset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.24/0.52         ((v5_relat_1 @ X16 @ X18)
% 0.24/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.52  thf('13', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      (((v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.24/0.52           (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['3', '9'])).
% 0.24/0.52  thf('15', plain,
% 0.24/0.52      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t3_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      (![X3 : $i, X5 : $i]:
% 0.24/0.52         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52        (k1_zfmisc_1 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf(t4_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.24/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.24/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.24/0.52          | (m1_subset_1 @ X6 @ X8))),
% 0.24/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((m1_subset_1 @ X0 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.24/0.52         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.24/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.52  thf('22', plain,
% 0.24/0.52      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.24/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((m1_subset_1 @ X0 @ (k1_relat_1 @ sk_E))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('demod', [status(thm)], ['19', '22'])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      ((((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ sk_B)
% 0.24/0.52        | (m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['14', '23'])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (![X1 : $i, X2 : $i]:
% 0.24/0.52         ((r2_hidden @ X1 @ X2)
% 0.24/0.52          | (v1_xboole_0 @ X2)
% 0.24/0.52          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      (((v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.24/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.52  thf(d8_partfun1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.52       ( ![C:$i]:
% 0.24/0.52         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.24/0.52           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.24/0.52          | ((k7_partfun1 @ X24 @ X23 @ X22) = (k1_funct_1 @ X23 @ X22))
% 0.24/0.52          | ~ (v1_funct_1 @ X23)
% 0.24/0.52          | ~ (v5_relat_1 @ X23 @ X24)
% 0.24/0.52          | ~ (v1_relat_1 @ X23))),
% 0.24/0.52      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.24/0.52          | ((sk_C) = (k1_xboole_0))
% 0.24/0.52          | (v1_xboole_0 @ sk_B)
% 0.24/0.52          | ~ (v1_relat_1 @ sk_E)
% 0.24/0.52          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.24/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.52          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.24/0.52              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(cc2_relat_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( v1_relat_1 @ A ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.24/0.52          | (v1_relat_1 @ X12)
% 0.24/0.52          | ~ (v1_relat_1 @ X13))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.52  thf('31', plain,
% 0.24/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.24/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.52  thf(fc6_relat_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.52  thf('33', plain, ((v1_relat_1 @ sk_E)),
% 0.24/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.24/0.52  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.24/0.52          | ((sk_C) = (k1_xboole_0))
% 0.24/0.52          | (v1_xboole_0 @ sk_B)
% 0.24/0.52          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.24/0.52          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.24/0.52              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.24/0.52      inference('demod', [status(thm)], ['28', '33', '34'])).
% 0.24/0.52  thf('36', plain,
% 0.24/0.52      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.24/0.52          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.24/0.52        | (v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ (k1_relat_1 @ sk_E)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['13', '35'])).
% 0.24/0.52  thf('37', plain,
% 0.24/0.52      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.24/0.52         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('38', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.24/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf('40', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(t185_funct_2, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.52       ( ![D:$i]:
% 0.24/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.24/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.24/0.52           ( ![E:$i]:
% 0.24/0.52             ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.52                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.24/0.52               ( ![F:$i]:
% 0.24/0.52                 ( ( m1_subset_1 @ F @ B ) =>
% 0.24/0.52                   ( ( r1_tarski @
% 0.24/0.52                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.24/0.52                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.24/0.52                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.52                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.24/0.52                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.24/0.52         (~ (v1_funct_1 @ X25)
% 0.24/0.52          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.24/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.24/0.52          | ~ (m1_subset_1 @ X28 @ X26)
% 0.24/0.52          | ((k1_funct_1 @ (k8_funct_2 @ X26 @ X27 @ X30 @ X25 @ X29) @ X28)
% 0.24/0.52              = (k1_funct_1 @ X29 @ (k1_funct_1 @ X25 @ X28)))
% 0.24/0.52          | ((X26) = (k1_xboole_0))
% 0.24/0.52          | ~ (r1_tarski @ (k2_relset_1 @ X26 @ X27 @ X25) @ 
% 0.24/0.52               (k1_relset_1 @ X27 @ X30 @ X29))
% 0.24/0.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X30)))
% 0.24/0.52          | ~ (v1_funct_1 @ X29)
% 0.24/0.52          | (v1_xboole_0 @ X27))),
% 0.24/0.52      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ sk_C)
% 0.24/0.52          | ~ (v1_funct_1 @ X0)
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.24/0.52          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.24/0.52          | ((sk_B) = (k1_xboole_0))
% 0.24/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.24/0.52              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.24/0.52          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.24/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.24/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.24/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.52  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('45', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ sk_C)
% 0.24/0.52          | ~ (v1_funct_1 @ X0)
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.24/0.52          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.24/0.52          | ((sk_B) = (k1_xboole_0))
% 0.24/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.24/0.52              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.24/0.52          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.24/0.52  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('47', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ sk_C)
% 0.24/0.52          | ~ (v1_funct_1 @ X0)
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.24/0.52          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.24/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.24/0.52              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.24/0.52          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.24/0.52  thf('48', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52             (k1_relat_1 @ sk_E))
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.24/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.24/0.52              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.24/0.52          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.24/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.52          | (v1_xboole_0 @ sk_C))),
% 0.24/0.52      inference('sup-', [status(thm)], ['39', '47'])).
% 0.24/0.52  thf('49', plain,
% 0.24/0.52      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('50', plain,
% 0.24/0.52      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.24/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf('51', plain,
% 0.24/0.52      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.24/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.24/0.52  thf('52', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('54', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.24/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.24/0.52              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.24/0.52          | (v1_xboole_0 @ sk_C))),
% 0.24/0.52      inference('demod', [status(thm)], ['48', '51', '52', '53'])).
% 0.24/0.52  thf('55', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('56', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.24/0.52            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.24/0.52          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['54', '55'])).
% 0.24/0.52  thf('57', plain,
% 0.24/0.52      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.24/0.52         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['38', '56'])).
% 0.24/0.52  thf('58', plain,
% 0.24/0.52      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.24/0.52         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.24/0.52      inference('demod', [status(thm)], ['37', '57'])).
% 0.24/0.52  thf('59', plain,
% 0.24/0.52      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.24/0.52          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.24/0.52        | (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ sk_B))),
% 0.24/0.52      inference('sup-', [status(thm)], ['36', '58'])).
% 0.24/0.52  thf('60', plain,
% 0.24/0.52      (((v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ (k1_relat_1 @ sk_E)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.24/0.52  thf(l13_xboole_0, axiom,
% 0.24/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.52  thf('61', plain,
% 0.24/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.24/0.52  thf('62', plain,
% 0.24/0.52      ((((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.24/0.52  thf('63', plain,
% 0.24/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.24/0.52  thf('64', plain,
% 0.24/0.52      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.24/0.52        | ((sk_C) = (k1_xboole_0))
% 0.24/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.24/0.52  thf('65', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('66', plain,
% 0.24/0.52      ((((k1_relat_1 @ sk_E) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.24/0.52  thf('67', plain,
% 0.24/0.52      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.24/0.52        (k1_zfmisc_1 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.52  thf(t5_subset, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.24/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.24/0.52  thf('68', plain,
% 0.24/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.24/0.52          | ~ (v1_xboole_0 @ X11)
% 0.24/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.24/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.52  thf('69', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.24/0.52  thf('70', plain,
% 0.24/0.52      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.24/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.52  thf('71', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.24/0.52  thf('72', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.52          | ((sk_C) = (k1_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['66', '71'])).
% 0.24/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.52  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.52  thf('74', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((sk_C) = (k1_xboole_0))
% 0.24/0.52          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.24/0.52      inference('demod', [status(thm)], ['72', '73'])).
% 0.24/0.52  thf('75', plain,
% 0.24/0.52      ((((sk_C) = (k1_xboole_0))
% 0.24/0.52        | (v1_xboole_0 @ sk_B)
% 0.24/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['10', '74'])).
% 0.24/0.52  thf('76', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (k1_xboole_0)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['75'])).
% 0.24/0.52  thf('77', plain,
% 0.24/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.24/0.52  thf('78', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.24/0.52  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('80', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.24/0.52  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.52  thf('82', plain, ($false),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '80', '81'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
