%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1055+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aeLUMaVX99

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:59 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 212 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  826 (3604 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k10_relat_1 @ X18 @ X16 ) @ ( k10_relat_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k10_relat_1 @ X0 @ sk_E ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( ( k7_relset_1 @ X4 @ X5 @ X3 @ X6 )
        = ( k9_relat_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_D ) ) @ ( k10_relat_1 @ X0 @ sk_E ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['9'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k8_relset_1 @ X8 @ X9 @ X7 @ X10 )
        = ( k10_relat_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['1'])).

thf('16',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k9_relat_1 @ X15 @ X13 ) @ ( k9_relat_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('27',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['21','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['9'])).

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
    inference('sat_resolution*',[status(thm)],['10','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_D ) ) @ ( k10_relat_1 @ X0 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['8','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( r1_tarski @ X25 @ ( k8_relset_1 @ X26 @ X28 @ X27 @ ( k7_relset_1 @ X26 @ X28 @ X27 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('51',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['9'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['10','31'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['51','56'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('58',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('59',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('60',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('61',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57','62'])).


%------------------------------------------------------------------------------
