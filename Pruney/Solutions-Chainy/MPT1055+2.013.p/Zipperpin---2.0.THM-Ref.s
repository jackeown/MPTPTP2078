%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EwE7fKRnG1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:35 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 295 expanded)
%              Number of leaves         :   39 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          : 1114 (5040 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t172_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                     => ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E )
                      <=> ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                       => ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E )
                        <=> ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t172_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['7'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X30 ) ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('10',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k9_relat_1 @ X25 @ X23 ) @ ( k9_relat_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k8_relset_1 @ X51 @ X52 @ X50 @ X53 )
        = ( k10_relat_1 @ X50 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('27',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['19','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['7'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['1'])).

thf('33',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ),
    inference('sat_resolution*',[status(thm)],['8','31','32'])).

thf('34',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['6','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ~ ( r1_tarski @ X65 @ X66 )
      | ( X68 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X68 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X68 ) ) )
      | ( r1_tarski @ X65 @ ( k8_relset_1 @ X66 @ X68 @ X67 @ ( k7_relset_1 @ X66 @ X68 @ X67 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('47',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( ( k7_relset_1 @ X54 @ X55 @ X56 @ X54 )
        = ( k2_relset_1 @ X54 @ X55 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('48',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X45 @ X43 )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('55',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( ( k8_relset_1 @ X57 @ X58 @ X59 @ ( k7_relset_1 @ X57 @ X58 @ X59 @ X57 ) )
        = ( k1_relset_1 @ X57 @ X58 @ X59 ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('56',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('58',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','52'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58','59','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','53','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('71',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k1_relat_1 @ X32 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X32 @ X31 ) @ X33 )
      | ( r1_tarski @ X31 @ ( k10_relat_1 @ X32 @ X33 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['7'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['8','31'])).

thf('81',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','81'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EwE7fKRnG1
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.97/2.20  % Solved by: fo/fo7.sh
% 1.97/2.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.20  % done 3350 iterations in 1.753s
% 1.97/2.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.97/2.20  % SZS output start Refutation
% 1.97/2.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.97/2.20  thf(sk_D_type, type, sk_D: $i).
% 1.97/2.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.20  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.97/2.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.97/2.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.97/2.20  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.97/2.20  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.97/2.20  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.97/2.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.20  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.97/2.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.97/2.20  thf(sk_C_type, type, sk_C: $i).
% 1.97/2.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.97/2.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.97/2.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.97/2.20  thf(sk_E_type, type, sk_E: $i).
% 1.97/2.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.97/2.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.20  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.20  thf(t172_funct_2, conjecture,
% 1.97/2.20    (![A:$i]:
% 1.97/2.20     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.97/2.20       ( ![B:$i]:
% 1.97/2.20         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.97/2.20           ( ![C:$i]:
% 1.97/2.20             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.20                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.20               ( ![D:$i]:
% 1.97/2.20                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.97/2.20                   ( ![E:$i]:
% 1.97/2.20                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.97/2.20                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.97/2.20                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.97/2.20  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.20    (~( ![A:$i]:
% 1.97/2.20        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.97/2.20          ( ![B:$i]:
% 1.97/2.20            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.97/2.20              ( ![C:$i]:
% 1.97/2.20                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.20                    ( m1_subset_1 @
% 1.97/2.20                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.20                  ( ![D:$i]:
% 1.97/2.20                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.97/2.20                      ( ![E:$i]:
% 1.97/2.20                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.97/2.20                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 1.97/2.20                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.97/2.20    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 1.97/2.20  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf('1', plain,
% 1.97/2.20      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.97/2.20        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf('2', plain,
% 1.97/2.20      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 1.97/2.20         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.97/2.20      inference('split', [status(esa)], ['1'])).
% 1.97/2.20  thf('3', plain,
% 1.97/2.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf(redefinition_k7_relset_1, axiom,
% 1.97/2.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.20       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.97/2.20  thf('4', plain,
% 1.97/2.20      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.97/2.20         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.97/2.20          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 1.97/2.20      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.97/2.20  thf('5', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.20  thf('6', plain,
% 1.97/2.20      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.97/2.20         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.97/2.20      inference('demod', [status(thm)], ['2', '5'])).
% 1.97/2.20  thf('7', plain,
% 1.97/2.20      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 1.97/2.20        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf('8', plain,
% 1.97/2.20      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 1.97/2.20       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.97/2.20      inference('split', [status(esa)], ['7'])).
% 1.97/2.20  thf(t145_funct_1, axiom,
% 1.97/2.20    (![A:$i,B:$i]:
% 1.97/2.20     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.97/2.20       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.97/2.20  thf('9', plain,
% 1.97/2.20      (![X29 : $i, X30 : $i]:
% 1.97/2.20         ((r1_tarski @ (k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X30)) @ X30)
% 1.97/2.20          | ~ (v1_funct_1 @ X29)
% 1.97/2.20          | ~ (v1_relat_1 @ X29))),
% 1.97/2.20      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.97/2.20  thf('10', plain,
% 1.97/2.20      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.97/2.20         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.20      inference('split', [status(esa)], ['1'])).
% 1.97/2.20  thf(t156_relat_1, axiom,
% 1.97/2.20    (![A:$i,B:$i,C:$i]:
% 1.97/2.20     ( ( v1_relat_1 @ C ) =>
% 1.97/2.20       ( ( r1_tarski @ A @ B ) =>
% 1.97/2.20         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.97/2.20  thf('11', plain,
% 1.97/2.20      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.97/2.20         (~ (r1_tarski @ X23 @ X24)
% 1.97/2.20          | ~ (v1_relat_1 @ X25)
% 1.97/2.20          | (r1_tarski @ (k9_relat_1 @ X25 @ X23) @ (k9_relat_1 @ X25 @ X24)))),
% 1.97/2.20      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.97/2.20  thf('12', plain,
% 1.97/2.20      ((![X0 : $i]:
% 1.97/2.20          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 1.97/2.20            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.97/2.20           | ~ (v1_relat_1 @ X0)))
% 1.97/2.20         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.97/2.20  thf('13', plain,
% 1.97/2.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf(redefinition_k8_relset_1, axiom,
% 1.97/2.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.20       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.97/2.20  thf('14', plain,
% 1.97/2.20      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.97/2.20         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 1.97/2.20          | ((k8_relset_1 @ X51 @ X52 @ X50 @ X53) = (k10_relat_1 @ X50 @ X53)))),
% 1.97/2.20      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.97/2.20  thf('15', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.20  thf('16', plain,
% 1.97/2.20      ((![X0 : $i]:
% 1.97/2.20          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 1.97/2.20            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.97/2.20           | ~ (v1_relat_1 @ X0)))
% 1.97/2.20         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.20      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.20  thf(t1_xboole_1, axiom,
% 1.97/2.20    (![A:$i,B:$i,C:$i]:
% 1.97/2.20     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.97/2.20       ( r1_tarski @ A @ C ) ))).
% 1.97/2.20  thf('17', plain,
% 1.97/2.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.97/2.20         (~ (r1_tarski @ X3 @ X4)
% 1.97/2.20          | ~ (r1_tarski @ X4 @ X5)
% 1.97/2.20          | (r1_tarski @ X3 @ X5))),
% 1.97/2.20      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.97/2.20  thf('18', plain,
% 1.97/2.20      ((![X0 : $i, X1 : $i]:
% 1.97/2.20          (~ (v1_relat_1 @ X0)
% 1.97/2.20           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 1.97/2.20           | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ 
% 1.97/2.20                X1)))
% 1.97/2.20         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.20      inference('sup-', [status(thm)], ['16', '17'])).
% 1.97/2.20  thf('19', plain,
% 1.97/2.20      (((~ (v1_relat_1 @ sk_C)
% 1.97/2.20         | ~ (v1_funct_1 @ sk_C)
% 1.97/2.20         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 1.97/2.20         | ~ (v1_relat_1 @ sk_C)))
% 1.97/2.20         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.20      inference('sup-', [status(thm)], ['9', '18'])).
% 1.97/2.20  thf('20', plain,
% 1.97/2.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf(cc2_relat_1, axiom,
% 1.97/2.20    (![A:$i]:
% 1.97/2.20     ( ( v1_relat_1 @ A ) =>
% 1.97/2.20       ( ![B:$i]:
% 1.97/2.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.97/2.20  thf('21', plain,
% 1.97/2.20      (![X17 : $i, X18 : $i]:
% 1.97/2.20         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.97/2.20          | (v1_relat_1 @ X17)
% 1.97/2.20          | ~ (v1_relat_1 @ X18))),
% 1.97/2.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.97/2.20  thf('22', plain,
% 1.97/2.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.97/2.20      inference('sup-', [status(thm)], ['20', '21'])).
% 1.97/2.20  thf(fc6_relat_1, axiom,
% 1.97/2.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.97/2.20  thf('23', plain,
% 1.97/2.20      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.97/2.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.97/2.20  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.20      inference('demod', [status(thm)], ['22', '23'])).
% 1.97/2.21  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.21      inference('demod', [status(thm)], ['22', '23'])).
% 1.97/2.21  thf('27', plain,
% 1.97/2.21      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.97/2.21         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.21      inference('demod', [status(thm)], ['19', '24', '25', '26'])).
% 1.97/2.21  thf('28', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.21  thf('29', plain,
% 1.97/2.21      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 1.97/2.21         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.97/2.21      inference('split', [status(esa)], ['7'])).
% 1.97/2.21  thf('30', plain,
% 1.97/2.21      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 1.97/2.21         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 1.97/2.21      inference('sup-', [status(thm)], ['28', '29'])).
% 1.97/2.21  thf('31', plain,
% 1.97/2.21      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 1.97/2.21       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.97/2.21      inference('sup-', [status(thm)], ['27', '30'])).
% 1.97/2.21  thf('32', plain,
% 1.97/2.21      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 1.97/2.21       ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.97/2.21      inference('split', [status(esa)], ['1'])).
% 1.97/2.21  thf('33', plain,
% 1.97/2.21      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 1.97/2.21      inference('sat_resolution*', [status(thm)], ['8', '31', '32'])).
% 1.97/2.21  thf('34', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 1.97/2.21      inference('simpl_trail', [status(thm)], ['6', '33'])).
% 1.97/2.21  thf(d10_xboole_0, axiom,
% 1.97/2.21    (![A:$i,B:$i]:
% 1.97/2.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.97/2.21  thf('35', plain,
% 1.97/2.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.97/2.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.21  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.97/2.21      inference('simplify', [status(thm)], ['35'])).
% 1.97/2.21  thf('37', plain,
% 1.97/2.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf(t50_funct_2, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.97/2.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.21       ( ( r1_tarski @ C @ A ) =>
% 1.97/2.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.97/2.21           ( r1_tarski @
% 1.97/2.21             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 1.97/2.21  thf('38', plain,
% 1.97/2.21      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 1.97/2.21         (~ (r1_tarski @ X65 @ X66)
% 1.97/2.21          | ((X68) = (k1_xboole_0))
% 1.97/2.21          | ~ (v1_funct_1 @ X67)
% 1.97/2.21          | ~ (v1_funct_2 @ X67 @ X66 @ X68)
% 1.97/2.21          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X68)))
% 1.97/2.21          | (r1_tarski @ X65 @ 
% 1.97/2.21             (k8_relset_1 @ X66 @ X68 @ X67 @ 
% 1.97/2.21              (k7_relset_1 @ X66 @ X68 @ X67 @ X65))))),
% 1.97/2.21      inference('cnf', [status(esa)], [t50_funct_2])).
% 1.97/2.21  thf('39', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((r1_tarski @ X0 @ 
% 1.97/2.21           (k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 1.97/2.21            (k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0)))
% 1.97/2.21          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.97/2.21          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.21          | ((sk_B) = (k1_xboole_0))
% 1.97/2.21          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.97/2.21      inference('sup-', [status(thm)], ['37', '38'])).
% 1.97/2.21  thf('40', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.21  thf('41', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.21  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('44', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)))
% 1.97/2.21          | ((sk_B) = (k1_xboole_0))
% 1.97/2.21          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.97/2.21      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 1.97/2.21  thf('45', plain,
% 1.97/2.21      ((((sk_B) = (k1_xboole_0))
% 1.97/2.21        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 1.97/2.21      inference('sup-', [status(thm)], ['36', '44'])).
% 1.97/2.21  thf('46', plain,
% 1.97/2.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf(t38_relset_1, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i]:
% 1.97/2.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.21       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.97/2.21         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.97/2.21  thf('47', plain,
% 1.97/2.21      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.97/2.21         (((k7_relset_1 @ X54 @ X55 @ X56 @ X54)
% 1.97/2.21            = (k2_relset_1 @ X54 @ X55 @ X56))
% 1.97/2.21          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 1.97/2.21      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.97/2.21  thf('48', plain,
% 1.97/2.21      (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.97/2.21         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 1.97/2.21      inference('sup-', [status(thm)], ['46', '47'])).
% 1.97/2.21  thf('49', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.21  thf('50', plain,
% 1.97/2.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf(redefinition_k2_relset_1, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i]:
% 1.97/2.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.97/2.21  thf('51', plain,
% 1.97/2.21      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.97/2.21         (((k2_relset_1 @ X44 @ X45 @ X43) = (k2_relat_1 @ X43))
% 1.97/2.21          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 1.97/2.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.21  thf('52', plain,
% 1.97/2.21      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.97/2.21      inference('sup-', [status(thm)], ['50', '51'])).
% 1.97/2.21  thf('53', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 1.97/2.21      inference('demod', [status(thm)], ['48', '49', '52'])).
% 1.97/2.21  thf('54', plain,
% 1.97/2.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf(t39_relset_1, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i]:
% 1.97/2.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.97/2.21       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 1.97/2.21           ( k2_relset_1 @ B @ A @ C ) ) & 
% 1.97/2.21         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 1.97/2.21           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 1.97/2.21  thf('55', plain,
% 1.97/2.21      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.97/2.21         (((k8_relset_1 @ X57 @ X58 @ X59 @ 
% 1.97/2.21            (k7_relset_1 @ X57 @ X58 @ X59 @ X57))
% 1.97/2.21            = (k1_relset_1 @ X57 @ X58 @ X59))
% 1.97/2.21          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 1.97/2.21      inference('cnf', [status(esa)], [t39_relset_1])).
% 1.97/2.21  thf('56', plain,
% 1.97/2.21      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ 
% 1.97/2.21         (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 1.97/2.21         = (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 1.97/2.21      inference('sup-', [status(thm)], ['54', '55'])).
% 1.97/2.21  thf('57', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.97/2.21  thf('58', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 1.97/2.21      inference('demod', [status(thm)], ['48', '49', '52'])).
% 1.97/2.21  thf('59', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.21  thf('60', plain,
% 1.97/2.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf(redefinition_k1_relset_1, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i]:
% 1.97/2.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.97/2.21  thf('61', plain,
% 1.97/2.21      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.97/2.21         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 1.97/2.21          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 1.97/2.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.21  thf('62', plain,
% 1.97/2.21      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.97/2.21      inference('sup-', [status(thm)], ['60', '61'])).
% 1.97/2.21  thf('63', plain,
% 1.97/2.21      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.97/2.21      inference('demod', [status(thm)], ['56', '57', '58', '59', '62'])).
% 1.97/2.21  thf('64', plain,
% 1.97/2.21      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)))),
% 1.97/2.21      inference('demod', [status(thm)], ['45', '53', '63'])).
% 1.97/2.21  thf('65', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf(t3_subset, axiom,
% 1.97/2.21    (![A:$i,B:$i]:
% 1.97/2.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.97/2.21  thf('66', plain,
% 1.97/2.21      (![X11 : $i, X12 : $i]:
% 1.97/2.21         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.97/2.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.21  thf('67', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.97/2.21      inference('sup-', [status(thm)], ['65', '66'])).
% 1.97/2.21  thf('68', plain,
% 1.97/2.21      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.97/2.21         (~ (r1_tarski @ X3 @ X4)
% 1.97/2.21          | ~ (r1_tarski @ X4 @ X5)
% 1.97/2.21          | (r1_tarski @ X3 @ X5))),
% 1.97/2.21      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.97/2.21  thf('69', plain,
% 1.97/2.21      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['67', '68'])).
% 1.97/2.21  thf('70', plain,
% 1.97/2.21      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 1.97/2.21      inference('sup-', [status(thm)], ['64', '69'])).
% 1.97/2.21  thf(t163_funct_1, axiom,
% 1.97/2.21    (![A:$i,B:$i,C:$i]:
% 1.97/2.21     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.97/2.21       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.97/2.21           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.97/2.21         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.97/2.21  thf('71', plain,
% 1.97/2.21      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.97/2.21         (~ (r1_tarski @ X31 @ (k1_relat_1 @ X32))
% 1.97/2.21          | ~ (r1_tarski @ (k9_relat_1 @ X32 @ X31) @ X33)
% 1.97/2.21          | (r1_tarski @ X31 @ (k10_relat_1 @ X32 @ X33))
% 1.97/2.21          | ~ (v1_funct_1 @ X32)
% 1.97/2.21          | ~ (v1_relat_1 @ X32))),
% 1.97/2.21      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.97/2.21  thf('72', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         (((sk_B) = (k1_xboole_0))
% 1.97/2.21          | ~ (v1_relat_1 @ sk_C)
% 1.97/2.21          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.21          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 1.97/2.21          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['70', '71'])).
% 1.97/2.21  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.21      inference('demod', [status(thm)], ['22', '23'])).
% 1.97/2.21  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.21  thf('75', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         (((sk_B) = (k1_xboole_0))
% 1.97/2.21          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 1.97/2.21          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 1.97/2.21      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.97/2.21  thf('76', plain,
% 1.97/2.21      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 1.97/2.21        | ((sk_B) = (k1_xboole_0)))),
% 1.97/2.21      inference('sup-', [status(thm)], ['34', '75'])).
% 1.97/2.21  thf('77', plain,
% 1.97/2.21      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 1.97/2.21         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.21      inference('split', [status(esa)], ['7'])).
% 1.97/2.21  thf('78', plain,
% 1.97/2.21      (![X0 : $i]:
% 1.97/2.21         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.97/2.21      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.21  thf('79', plain,
% 1.97/2.21      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 1.97/2.21         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 1.97/2.21      inference('demod', [status(thm)], ['77', '78'])).
% 1.97/2.21  thf('80', plain,
% 1.97/2.21      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.97/2.21      inference('sat_resolution*', [status(thm)], ['8', '31'])).
% 1.97/2.21  thf('81', plain, (~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 1.97/2.21      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 1.97/2.21  thf('82', plain, (((sk_B) = (k1_xboole_0))),
% 1.97/2.21      inference('clc', [status(thm)], ['76', '81'])).
% 1.97/2.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.97/2.21  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.97/2.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.97/2.21  thf('84', plain, ($false),
% 1.97/2.21      inference('demod', [status(thm)], ['0', '82', '83'])).
% 1.97/2.21  
% 1.97/2.21  % SZS output end Refutation
% 1.97/2.21  
% 1.97/2.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
