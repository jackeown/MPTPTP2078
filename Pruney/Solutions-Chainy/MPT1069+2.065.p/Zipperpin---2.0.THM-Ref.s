%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YNkkfWi0j3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 156 expanded)
%              Number of leaves         :   39 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  981 (3333 expanded)
%              Number of equality atoms :   48 ( 140 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X35 @ X32 ) @ ( k2_relset_1 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k7_partfun1 @ X25 @ X24 @ X23 )
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['23','28','29'])).

thf('31',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','30'])).

thf('32',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ X27 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X27 @ X28 @ X31 @ X26 @ X30 ) @ X29 )
        = ( k1_funct_1 @ X30 @ ( k1_funct_1 @ X26 @ X29 ) ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X27 @ X28 @ X26 ) @ ( k1_relset_1 @ X28 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('46',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['43','46','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['33','51'])).

thf('53',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['32','52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','53'])).

thf('55',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('56',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('61',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YNkkfWi0j3
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 114 iterations in 0.053s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(t186_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.51           ( ![E:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.51               ( ![F:$i]:
% 0.20/0.51                 ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.51                   ( ( r1_tarski @
% 0.20/0.51                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.51                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.51                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.51                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.51          ( ![D:$i]:
% 0.20/0.51            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.51                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.51              ( ![E:$i]:
% 0.20/0.51                ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                    ( m1_subset_1 @
% 0.20/0.51                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.51                  ( ![F:$i]:
% 0.20/0.51                    ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.51                      ( ( r1_tarski @
% 0.20/0.51                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.51                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.51                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51                          ( ( k1_funct_1 @
% 0.20/0.51                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.51                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.20/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         ((v5_relat_1 @ X17 @ X19)
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((r2_hidden @ X9 @ X10)
% 0.20/0.51          | (v1_xboole_0 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('6', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t6_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X32 @ X33)
% 0.20/0.51          | ((X34) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_funct_1 @ X35)
% 0.20/0.51          | ~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.20/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X35 @ X32) @ 
% 0.20/0.51             (k2_relset_1 @ X33 @ X34 @ X35)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.20/0.51           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.20/0.51           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.20/0.51          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.20/0.51           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | (r2_hidden @ X3 @ X5)
% 0.20/0.51          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.51        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '20'])).
% 0.20/0.51  thf(d8_partfun1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.51           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.20/0.51          | ((k7_partfun1 @ X25 @ X24 @ X23) = (k1_funct_1 @ X24 @ X23))
% 0.20/0.51          | ~ (v1_funct_1 @ X24)
% 0.20/0.51          | ~ (v5_relat_1 @ X24 @ X25)
% 0.20/0.51          | ~ (v1_relat_1 @ X24))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_B_1)
% 0.20/0.51          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ sk_E)
% 0.20/0.51          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.20/0.51          | (v1_relat_1 @ X11)
% 0.20/0.51          | ~ (v1_relat_1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('28', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_B_1)
% 0.20/0.51          | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.20/0.51          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.51          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0))
% 0.20/0.51        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.51         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t185_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.51           ( ![E:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.20/0.51               ( ![F:$i]:
% 0.20/0.51                 ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.51                   ( ( r1_tarski @
% 0.20/0.51                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.20/0.51                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.20/0.51                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.20/0.51                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.51         (~ (v1_funct_1 @ X26)
% 0.20/0.51          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.20/0.51          | ~ (m1_subset_1 @ X29 @ X27)
% 0.20/0.51          | ((k1_funct_1 @ (k8_funct_2 @ X27 @ X28 @ X31 @ X26 @ X30) @ X29)
% 0.20/0.51              = (k1_funct_1 @ X30 @ (k1_funct_1 @ X26 @ X29)))
% 0.20/0.51          | ((X27) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ (k2_relset_1 @ X27 @ X28 @ X26) @ 
% 0.20/0.51               (k1_relset_1 @ X28 @ X31 @ X30))
% 0.20/0.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X31)))
% 0.20/0.51          | ~ (v1_funct_1 @ X30)
% 0.20/0.51          | (v1_xboole_0 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_C_1)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.20/0.51          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.20/0.51          | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_C_1)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.20/0.51          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.20/0.51          | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.51  thf('41', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ sk_C_1)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.20/0.51          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.20/0.51          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51             (k1_relat_1 @ sk_E))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.20/0.51          | ((k1_funct_1 @ 
% 0.20/0.51              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.20/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.51          | ~ (m1_subset_1 @ sk_E @ 
% 0.20/0.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | (v1_xboole_0 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.20/0.51        (k1_relat_1 @ sk_E))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.20/0.51          | ((k1_funct_1 @ 
% 0.20/0.51              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.20/0.51              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.51          | (v1_xboole_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '46', '47', '48'])).
% 0.20/0.51  thf('50', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.51            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.20/0.51         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.51         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.51          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.51        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '53'])).
% 0.20/0.51  thf('55', plain, ((((sk_C_1) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('57', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.51  thf('58', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('60', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf(d1_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf(t7_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.51  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.51  thf('65', plain, ($false),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '59', '64'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
