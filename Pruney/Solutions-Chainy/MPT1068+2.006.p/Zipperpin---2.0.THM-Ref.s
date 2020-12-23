%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D2qaRR40l4

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:57 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 247 expanded)
%              Number of leaves         :   46 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          : 1257 (4863 expanded)
%              Number of equality atoms :   77 ( 222 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t185_funct_2,conjecture,(
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
                          = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t185_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('5',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( X71 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_funct_2 @ X70 @ X69 @ X71 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X71 ) ) )
      | ( ( k8_relset_1 @ X69 @ X71 @ X70 @ X71 )
        = X69 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('6',plain,
    ( ( ( k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_C_1 )
      = sk_B_1 )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( ( k8_relset_1 @ X52 @ X53 @ X51 @ X54 )
        = ( k10_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_C_1 )
      = sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( m1_subset_1 @ X0 @ ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ sk_F @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
    | ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k1_funct_1 @ X37 @ ( k1_funct_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X39 @ ( k1_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('35',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_funct_1 @ X66 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X68 ) ) )
      | ( ( k1_partfun1 @ X64 @ X65 @ X67 @ X68 @ X63 @ X66 )
        = ( k5_relat_1 @ X63 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X50 @ X48 )
        = ( k2_relat_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( ( k8_funct_2 @ X61 @ X59 @ X60 @ X62 @ X58 )
        = ( k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X61 @ X59 @ X62 ) @ ( k1_relset_1 @ X59 @ X60 @ X58 ) )
      | ( X59 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X61 @ X59 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relset_1 @ X46 @ X47 @ X45 )
        = ( k1_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
    | ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','58','59','60','61'])).

thf('63',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','62'])).

thf('64',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('76',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('77',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('81',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','81'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('83',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('84',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('91',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D2qaRR40l4
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.68/1.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.68/1.92  % Solved by: fo/fo7.sh
% 1.68/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.92  % done 2775 iterations in 1.455s
% 1.68/1.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.68/1.92  % SZS output start Refutation
% 1.68/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.68/1.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.68/1.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.68/1.92  thf(sk_E_type, type, sk_E: $i).
% 1.68/1.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.68/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.68/1.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.68/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.68/1.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.68/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.92  thf(sk_B_type, type, sk_B: $i > $i).
% 1.68/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.68/1.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.68/1.92  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 1.68/1.92  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.68/1.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.68/1.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.68/1.92  thf(sk_F_type, type, sk_F: $i).
% 1.68/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.68/1.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.68/1.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.68/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.68/1.92  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.68/1.92  thf(sk_D_type, type, sk_D: $i).
% 1.68/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.68/1.92  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.68/1.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.68/1.92  thf(t185_funct_2, conjecture,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.68/1.92       ( ![D:$i]:
% 1.68/1.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.68/1.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.68/1.92           ( ![E:$i]:
% 1.68/1.92             ( ( ( v1_funct_1 @ E ) & 
% 1.68/1.92                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.68/1.92               ( ![F:$i]:
% 1.68/1.92                 ( ( m1_subset_1 @ F @ B ) =>
% 1.68/1.92                   ( ( r1_tarski @
% 1.68/1.92                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.68/1.92                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.68/1.92                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.68/1.92                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.68/1.92                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.68/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.92    (~( ![A:$i,B:$i,C:$i]:
% 1.68/1.92        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.68/1.92          ( ![D:$i]:
% 1.68/1.92            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.68/1.92                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.68/1.92              ( ![E:$i]:
% 1.68/1.92                ( ( ( v1_funct_1 @ E ) & 
% 1.68/1.92                    ( m1_subset_1 @
% 1.68/1.92                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.68/1.92                  ( ![F:$i]:
% 1.68/1.92                    ( ( m1_subset_1 @ F @ B ) =>
% 1.68/1.92                      ( ( r1_tarski @
% 1.68/1.92                          ( k2_relset_1 @ B @ C @ D ) @ 
% 1.68/1.92                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.68/1.92                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.68/1.92                          ( ( k1_funct_1 @
% 1.68/1.92                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.68/1.92                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.68/1.92    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 1.68/1.92  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(t2_subset, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( m1_subset_1 @ A @ B ) =>
% 1.68/1.92       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.68/1.92  thf('2', plain,
% 1.68/1.92      (![X11 : $i, X12 : $i]:
% 1.68/1.92         ((r2_hidden @ X11 @ X12)
% 1.68/1.92          | (v1_xboole_0 @ X12)
% 1.68/1.92          | ~ (m1_subset_1 @ X11 @ X12))),
% 1.68/1.92      inference('cnf', [status(esa)], [t2_subset])).
% 1.68/1.92  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 1.68/1.92      inference('sup-', [status(thm)], ['1', '2'])).
% 1.68/1.92  thf('4', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(t48_funct_2, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.68/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.68/1.92         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 1.68/1.92  thf('5', plain,
% 1.68/1.92      (![X69 : $i, X70 : $i, X71 : $i]:
% 1.68/1.92         (((X71) = (k1_xboole_0))
% 1.68/1.92          | ~ (v1_funct_1 @ X70)
% 1.68/1.92          | ~ (v1_funct_2 @ X70 @ X69 @ X71)
% 1.68/1.92          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X71)))
% 1.68/1.92          | ((k8_relset_1 @ X69 @ X71 @ X70 @ X71) = (X69)))),
% 1.68/1.92      inference('cnf', [status(esa)], [t48_funct_2])).
% 1.68/1.92  thf('6', plain,
% 1.68/1.92      ((((k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_C_1) = (sk_B_1))
% 1.68/1.92        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 1.68/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['4', '5'])).
% 1.68/1.92  thf('7', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(redefinition_k8_relset_1, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.92       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.68/1.92  thf('8', plain,
% 1.68/1.92      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.68/1.92         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.68/1.92          | ((k8_relset_1 @ X52 @ X53 @ X51 @ X54) = (k10_relat_1 @ X51 @ X54)))),
% 1.68/1.92      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.68/1.92  thf('9', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         ((k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D @ X0)
% 1.68/1.92           = (k10_relat_1 @ sk_D @ X0))),
% 1.68/1.92      inference('sup-', [status(thm)], ['7', '8'])).
% 1.68/1.92  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('12', plain,
% 1.68/1.92      ((((k10_relat_1 @ sk_D @ sk_C_1) = (sk_B_1)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 1.68/1.92  thf(t167_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ B ) =>
% 1.68/1.92       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.68/1.92  thf('13', plain,
% 1.68/1.92      (![X30 : $i, X31 : $i]:
% 1.68/1.92         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 1.68/1.92          | ~ (v1_relat_1 @ X30))),
% 1.68/1.92      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.68/1.92  thf('14', plain,
% 1.68/1.92      (((r1_tarski @ sk_B_1 @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.92      inference('sup+', [status(thm)], ['12', '13'])).
% 1.68/1.92  thf('15', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(cc2_relat_1, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_relat_1 @ A ) =>
% 1.68/1.92       ( ![B:$i]:
% 1.68/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.68/1.92  thf('16', plain,
% 1.68/1.92      (![X19 : $i, X20 : $i]:
% 1.68/1.92         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.68/1.92          | (v1_relat_1 @ X19)
% 1.68/1.92          | ~ (v1_relat_1 @ X20))),
% 1.68/1.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.68/1.92  thf('17', plain,
% 1.68/1.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)) | (v1_relat_1 @ sk_D))),
% 1.68/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.68/1.92  thf(fc6_relat_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.68/1.92  thf('18', plain,
% 1.68/1.92      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.68/1.92  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.92      inference('demod', [status(thm)], ['17', '18'])).
% 1.68/1.92  thf('20', plain,
% 1.68/1.92      (((r1_tarski @ sk_B_1 @ (k1_relat_1 @ sk_D)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('demod', [status(thm)], ['14', '19'])).
% 1.68/1.92  thf(t3_subset, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.68/1.92  thf('21', plain,
% 1.68/1.92      (![X13 : $i, X15 : $i]:
% 1.68/1.92         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.68/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.68/1.92  thf('22', plain,
% 1.68/1.92      ((((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 1.68/1.92      inference('sup-', [status(thm)], ['20', '21'])).
% 1.68/1.92  thf(t4_subset, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.68/1.92       ( m1_subset_1 @ A @ C ) ))).
% 1.68/1.92  thf('23', plain,
% 1.68/1.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.68/1.92         (~ (r2_hidden @ X16 @ X17)
% 1.68/1.92          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.68/1.92          | (m1_subset_1 @ X16 @ X18))),
% 1.68/1.92      inference('cnf', [status(esa)], [t4_subset])).
% 1.68/1.92  thf('24', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         (((sk_C_1) = (k1_xboole_0))
% 1.68/1.92          | (m1_subset_1 @ X0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.68/1.92      inference('sup-', [status(thm)], ['22', '23'])).
% 1.68/1.92  thf('25', plain,
% 1.68/1.92      (((v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | (m1_subset_1 @ sk_F @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['3', '24'])).
% 1.68/1.92  thf('26', plain,
% 1.68/1.92      (![X11 : $i, X12 : $i]:
% 1.68/1.92         ((r2_hidden @ X11 @ X12)
% 1.68/1.92          | (v1_xboole_0 @ X12)
% 1.68/1.92          | ~ (m1_subset_1 @ X11 @ X12))),
% 1.68/1.92      inference('cnf', [status(esa)], [t2_subset])).
% 1.68/1.92  thf('27', plain,
% 1.68/1.92      ((((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | (v1_xboole_0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['25', '26'])).
% 1.68/1.92  thf(t23_funct_1, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.68/1.92       ( ![C:$i]:
% 1.68/1.92         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.68/1.92           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.68/1.92             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.68/1.92               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 1.68/1.92  thf('28', plain,
% 1.68/1.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.68/1.92         (~ (v1_relat_1 @ X37)
% 1.68/1.92          | ~ (v1_funct_1 @ X37)
% 1.68/1.92          | ((k1_funct_1 @ (k5_relat_1 @ X38 @ X37) @ X39)
% 1.68/1.92              = (k1_funct_1 @ X37 @ (k1_funct_1 @ X38 @ X39)))
% 1.68/1.92          | ~ (r2_hidden @ X39 @ (k1_relat_1 @ X38))
% 1.68/1.92          | ~ (v1_funct_1 @ X38)
% 1.68/1.92          | ~ (v1_relat_1 @ X38))),
% 1.68/1.92      inference('cnf', [status(esa)], [t23_funct_1])).
% 1.68/1.92  thf('29', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         ((v1_xboole_0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92          | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92          | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92          | ~ (v1_relat_1 @ sk_D)
% 1.68/1.92          | ~ (v1_funct_1 @ sk_D)
% 1.68/1.92          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 1.68/1.92              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.68/1.92          | ~ (v1_funct_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X0))),
% 1.68/1.92      inference('sup-', [status(thm)], ['27', '28'])).
% 1.68/1.92  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.92      inference('demod', [status(thm)], ['17', '18'])).
% 1.68/1.92  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('32', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         ((v1_xboole_0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92          | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92          | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 1.68/1.92              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.68/1.92          | ~ (v1_funct_1 @ X0)
% 1.68/1.92          | ~ (v1_relat_1 @ X0))),
% 1.68/1.92      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.68/1.92  thf('33', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('34', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(redefinition_k1_partfun1, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.68/1.92     ( ( ( v1_funct_1 @ E ) & 
% 1.68/1.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.68/1.92         ( v1_funct_1 @ F ) & 
% 1.68/1.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.68/1.92       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.68/1.92  thf('35', plain,
% 1.68/1.92      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 1.68/1.92         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 1.68/1.92          | ~ (v1_funct_1 @ X63)
% 1.68/1.92          | ~ (v1_funct_1 @ X66)
% 1.68/1.92          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X68)))
% 1.68/1.92          | ((k1_partfun1 @ X64 @ X65 @ X67 @ X68 @ X63 @ X66)
% 1.68/1.92              = (k5_relat_1 @ X63 @ X66)))),
% 1.68/1.92      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.68/1.92  thf('36', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.92         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 1.68/1.92            = (k5_relat_1 @ sk_D @ X0))
% 1.68/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.68/1.92          | ~ (v1_funct_1 @ X0)
% 1.68/1.92          | ~ (v1_funct_1 @ sk_D))),
% 1.68/1.92      inference('sup-', [status(thm)], ['34', '35'])).
% 1.68/1.92  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('38', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.92         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 1.68/1.92            = (k5_relat_1 @ sk_D @ X0))
% 1.68/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.68/1.92          | ~ (v1_funct_1 @ X0))),
% 1.68/1.92      inference('demod', [status(thm)], ['36', '37'])).
% 1.68/1.92  thf('39', plain,
% 1.68/1.92      ((~ (v1_funct_1 @ sk_E)
% 1.68/1.92        | ((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 1.68/1.92            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['33', '38'])).
% 1.68/1.92  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('41', plain,
% 1.68/1.92      (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 1.68/1.92         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.68/1.92      inference('demod', [status(thm)], ['39', '40'])).
% 1.68/1.92  thf('42', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(redefinition_k2_relset_1, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.68/1.92  thf('43', plain,
% 1.68/1.92      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.68/1.92         (((k2_relset_1 @ X49 @ X50 @ X48) = (k2_relat_1 @ X48))
% 1.68/1.92          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 1.68/1.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.68/1.92  thf('44', plain,
% 1.68/1.92      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.68/1.92      inference('sup-', [status(thm)], ['42', '43'])).
% 1.68/1.92  thf('45', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(d12_funct_2, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.68/1.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.92       ( ![E:$i]:
% 1.68/1.92         ( ( ( v1_funct_1 @ E ) & 
% 1.68/1.92             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.68/1.92           ( ( r1_tarski @
% 1.68/1.92               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 1.68/1.92             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.68/1.92               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 1.68/1.92                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 1.68/1.92  thf('46', plain,
% 1.68/1.92      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 1.68/1.92         (~ (v1_funct_1 @ X58)
% 1.68/1.92          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 1.68/1.92          | ((k8_funct_2 @ X61 @ X59 @ X60 @ X62 @ X58)
% 1.68/1.92              = (k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58))
% 1.68/1.92          | ~ (r1_tarski @ (k2_relset_1 @ X61 @ X59 @ X62) @ 
% 1.68/1.92               (k1_relset_1 @ X59 @ X60 @ X58))
% 1.68/1.92          | ((X59) = (k1_xboole_0))
% 1.68/1.92          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 1.68/1.92          | ~ (v1_funct_2 @ X62 @ X61 @ X59)
% 1.68/1.92          | ~ (v1_funct_1 @ X62))),
% 1.68/1.92      inference('cnf', [status(esa)], [d12_funct_2])).
% 1.68/1.92  thf('47', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_funct_1 @ X0)
% 1.68/1.92          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 1.68/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 1.68/1.92          | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 1.68/1.92               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 1.68/1.92          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 1.68/1.92              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E))
% 1.68/1.92          | ~ (v1_funct_1 @ sk_E))),
% 1.68/1.92      inference('sup-', [status(thm)], ['45', '46'])).
% 1.68/1.92  thf('48', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf(redefinition_k1_relset_1, axiom,
% 1.68/1.92    (![A:$i,B:$i,C:$i]:
% 1.68/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.68/1.92  thf('49', plain,
% 1.68/1.92      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.68/1.92         (((k1_relset_1 @ X46 @ X47 @ X45) = (k1_relat_1 @ X45))
% 1.68/1.92          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 1.68/1.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.68/1.92  thf('50', plain,
% 1.68/1.92      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.68/1.92      inference('sup-', [status(thm)], ['48', '49'])).
% 1.68/1.92  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('52', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]:
% 1.68/1.92         (~ (v1_funct_1 @ X0)
% 1.68/1.92          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 1.68/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 1.68/1.92          | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 1.68/1.92               (k1_relat_1 @ sk_E))
% 1.68/1.92          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 1.68/1.92              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E)))),
% 1.68/1.92      inference('demod', [status(thm)], ['47', '50', '51'])).
% 1.68/1.92  thf('53', plain,
% 1.68/1.92      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 1.68/1.92        | ((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 1.68/1.92            = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | ~ (m1_subset_1 @ sk_D @ 
% 1.68/1.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))
% 1.68/1.92        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 1.68/1.92        | ~ (v1_funct_1 @ sk_D))),
% 1.68/1.92      inference('sup-', [status(thm)], ['44', '52'])).
% 1.68/1.92  thf('54', plain,
% 1.68/1.92      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 1.68/1.92        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('55', plain,
% 1.68/1.92      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.68/1.92      inference('sup-', [status(thm)], ['48', '49'])).
% 1.68/1.92  thf('56', plain,
% 1.68/1.92      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 1.68/1.92        (k1_relat_1 @ sk_E))),
% 1.68/1.92      inference('demod', [status(thm)], ['54', '55'])).
% 1.68/1.92  thf('57', plain,
% 1.68/1.92      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.68/1.92      inference('sup-', [status(thm)], ['42', '43'])).
% 1.68/1.92  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.68/1.92      inference('demod', [status(thm)], ['56', '57'])).
% 1.68/1.92  thf('59', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('62', plain,
% 1.68/1.92      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 1.68/1.92          = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('demod', [status(thm)], ['53', '58', '59', '60', '61'])).
% 1.68/1.92  thf('63', plain,
% 1.68/1.92      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 1.68/1.92          = (k5_relat_1 @ sk_D @ sk_E))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup+', [status(thm)], ['41', '62'])).
% 1.68/1.92  thf('64', plain,
% 1.68/1.92      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 1.68/1.92         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('65', plain,
% 1.68/1.92      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 1.68/1.92          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['63', '64'])).
% 1.68/1.92  thf('66', plain,
% 1.68/1.92      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 1.68/1.92          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 1.68/1.92        | ~ (v1_relat_1 @ sk_E)
% 1.68/1.92        | ~ (v1_funct_1 @ sk_E)
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | (v1_xboole_0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['32', '65'])).
% 1.68/1.92  thf('67', plain,
% 1.68/1.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('68', plain,
% 1.68/1.92      (![X19 : $i, X20 : $i]:
% 1.68/1.92         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.68/1.92          | (v1_relat_1 @ X19)
% 1.68/1.92          | ~ (v1_relat_1 @ X20))),
% 1.68/1.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.68/1.92  thf('69', plain,
% 1.68/1.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 1.68/1.92      inference('sup-', [status(thm)], ['67', '68'])).
% 1.68/1.92  thf('70', plain,
% 1.68/1.92      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 1.68/1.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.68/1.92  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 1.68/1.92      inference('demod', [status(thm)], ['69', '70'])).
% 1.68/1.92  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('73', plain,
% 1.68/1.92      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 1.68/1.92          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | (v1_xboole_0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('demod', [status(thm)], ['66', '71', '72'])).
% 1.68/1.92  thf('74', plain,
% 1.68/1.92      (((v1_xboole_0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('simplify', [status(thm)], ['73'])).
% 1.68/1.92  thf('75', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 1.68/1.92      inference('sup-', [status(thm)], ['1', '2'])).
% 1.68/1.92  thf('76', plain,
% 1.68/1.92      (((r1_tarski @ sk_B_1 @ (k1_relat_1 @ sk_D)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('demod', [status(thm)], ['14', '19'])).
% 1.68/1.92  thf(d3_tarski, axiom,
% 1.68/1.92    (![A:$i,B:$i]:
% 1.68/1.92     ( ( r1_tarski @ A @ B ) <=>
% 1.68/1.92       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.68/1.92  thf('77', plain,
% 1.68/1.92      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.68/1.92         (~ (r2_hidden @ X3 @ X4)
% 1.68/1.92          | (r2_hidden @ X3 @ X5)
% 1.68/1.92          | ~ (r1_tarski @ X4 @ X5))),
% 1.68/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.68/1.92  thf('78', plain,
% 1.68/1.92      (![X0 : $i]:
% 1.68/1.92         (((sk_C_1) = (k1_xboole_0))
% 1.68/1.92          | (r2_hidden @ X0 @ (k1_relat_1 @ sk_D))
% 1.68/1.92          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.68/1.92      inference('sup-', [status(thm)], ['76', '77'])).
% 1.68/1.92  thf('79', plain,
% 1.68/1.92      (((v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D))
% 1.68/1.92        | ((sk_C_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['75', '78'])).
% 1.68/1.92  thf(d1_xboole_0, axiom,
% 1.68/1.92    (![A:$i]:
% 1.68/1.92     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.68/1.92  thf('80', plain,
% 1.68/1.92      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.68/1.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.68/1.92  thf('81', plain,
% 1.68/1.92      ((((sk_C_1) = (k1_xboole_0))
% 1.68/1.92        | (v1_xboole_0 @ sk_B_1)
% 1.68/1.92        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_D)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.68/1.92  thf('82', plain, ((((sk_C_1) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1))),
% 1.68/1.92      inference('clc', [status(thm)], ['74', '81'])).
% 1.68/1.92  thf(l13_xboole_0, axiom,
% 1.68/1.92    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.68/1.92  thf('83', plain,
% 1.68/1.92      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.68/1.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.68/1.92  thf('84', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['82', '83'])).
% 1.68/1.92  thf('85', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.68/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.92  thf('86', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.68/1.92      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 1.68/1.92  thf(t4_subset_1, axiom,
% 1.68/1.92    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.68/1.92  thf('87', plain,
% 1.68/1.92      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.68/1.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.68/1.92  thf('88', plain,
% 1.68/1.92      (![X13 : $i, X14 : $i]:
% 1.68/1.92         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.68/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.68/1.92  thf('89', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.68/1.92      inference('sup-', [status(thm)], ['87', '88'])).
% 1.68/1.92  thf('90', plain,
% 1.68/1.92      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.68/1.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.68/1.92  thf(t7_ordinal1, axiom,
% 1.68/1.92    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.68/1.92  thf('91', plain,
% 1.68/1.92      (![X40 : $i, X41 : $i]:
% 1.68/1.92         (~ (r2_hidden @ X40 @ X41) | ~ (r1_tarski @ X41 @ X40))),
% 1.68/1.92      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.68/1.92  thf('92', plain,
% 1.68/1.92      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.68/1.92      inference('sup-', [status(thm)], ['90', '91'])).
% 1.68/1.92  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.68/1.92      inference('sup-', [status(thm)], ['89', '92'])).
% 1.68/1.92  thf('94', plain, ($false),
% 1.68/1.92      inference('demod', [status(thm)], ['0', '86', '93'])).
% 1.68/1.92  
% 1.68/1.92  % SZS output end Refutation
% 1.68/1.92  
% 1.68/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
