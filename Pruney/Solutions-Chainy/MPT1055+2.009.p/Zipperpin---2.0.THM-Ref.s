%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.37GQXYg8hE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:35 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 172 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  904 (2858 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('9',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X31 ) ) )
      | ( ( k8_relset_1 @ X29 @ X31 @ X30 @ X31 )
        = X29 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('10',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13','14','15'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X16 @ X15 ) @ X17 )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('47',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X10 @ X8 ) @ ( k9_relat_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
          = ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) )
          = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('56',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('61',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.37GQXYg8hE
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.05  % Solved by: fo/fo7.sh
% 0.85/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.05  % done 799 iterations in 0.598s
% 0.85/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.05  % SZS output start Refutation
% 0.85/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.85/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.85/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.85/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.85/1.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.05  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.85/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.85/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.05  thf(sk_D_type, type, sk_D: $i).
% 0.85/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.85/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.85/1.05  thf(sk_E_type, type, sk_E: $i).
% 0.85/1.05  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.85/1.05  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.85/1.05  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.85/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.05  thf(t172_funct_2, conjecture,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.85/1.05       ( ![B:$i]:
% 0.85/1.05         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.85/1.05           ( ![C:$i]:
% 0.85/1.05             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.05                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.05               ( ![D:$i]:
% 0.85/1.05                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.05                   ( ![E:$i]:
% 0.85/1.05                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.85/1.05                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.85/1.05                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.85/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.05    (~( ![A:$i]:
% 0.85/1.05        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.85/1.05          ( ![B:$i]:
% 0.85/1.05            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.85/1.05              ( ![C:$i]:
% 0.85/1.05                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.05                    ( m1_subset_1 @
% 0.85/1.05                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.05                  ( ![D:$i]:
% 0.85/1.05                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.05                      ( ![E:$i]:
% 0.85/1.05                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.85/1.05                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.85/1.05                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.85/1.05    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 0.85/1.05  thf('0', plain,
% 0.85/1.05      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.85/1.05        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('1', plain,
% 0.85/1.05      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.85/1.05       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.85/1.05      inference('split', [status(esa)], ['0'])).
% 0.85/1.05  thf('2', plain,
% 0.85/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf(redefinition_k7_relset_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.05       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.85/1.05  thf('3', plain,
% 0.85/1.05      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.85/1.05         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.85/1.05          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.85/1.05      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.85/1.05  thf('4', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.05  thf('5', plain,
% 0.85/1.05      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.85/1.05        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('6', plain,
% 0.85/1.05      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.85/1.05         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('split', [status(esa)], ['5'])).
% 0.85/1.05  thf('7', plain,
% 0.85/1.05      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.85/1.05         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('sup+', [status(thm)], ['4', '6'])).
% 0.85/1.05  thf('8', plain,
% 0.85/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf(t48_funct_2, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.85/1.05         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.85/1.05  thf('9', plain,
% 0.85/1.05      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.85/1.05         (((X31) = (k1_xboole_0))
% 0.85/1.05          | ~ (v1_funct_1 @ X30)
% 0.85/1.05          | ~ (v1_funct_2 @ X30 @ X29 @ X31)
% 0.85/1.05          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X31)))
% 0.85/1.05          | ((k8_relset_1 @ X29 @ X31 @ X30 @ X31) = (X29)))),
% 0.85/1.05      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.85/1.05  thf('10', plain,
% 0.85/1.05      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) = (sk_A))
% 0.85/1.05        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.85/1.05        | ~ (v1_funct_1 @ sk_C)
% 0.85/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['8', '9'])).
% 0.85/1.05  thf('11', plain,
% 0.85/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf(redefinition_k8_relset_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.05       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.85/1.05  thf('12', plain,
% 0.85/1.05      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.85/1.05         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.85/1.05          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.85/1.05      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.85/1.05  thf('13', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.05  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('16', plain,
% 0.85/1.05      ((((k10_relat_1 @ sk_C @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.05      inference('demod', [status(thm)], ['10', '13', '14', '15'])).
% 0.85/1.05  thf(t167_relat_1, axiom,
% 0.85/1.05    (![A:$i,B:$i]:
% 0.85/1.05     ( ( v1_relat_1 @ B ) =>
% 0.85/1.05       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.85/1.05  thf('17', plain,
% 0.85/1.05      (![X11 : $i, X12 : $i]:
% 0.85/1.05         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 0.85/1.05          | ~ (v1_relat_1 @ X11))),
% 0.85/1.05      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.85/1.05  thf('18', plain,
% 0.85/1.05      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 0.85/1.05        | ((sk_B) = (k1_xboole_0))
% 0.85/1.05        | ~ (v1_relat_1 @ sk_C))),
% 0.85/1.05      inference('sup+', [status(thm)], ['16', '17'])).
% 0.85/1.05  thf('19', plain,
% 0.85/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf(cc1_relset_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.05       ( v1_relat_1 @ C ) ))).
% 0.85/1.05  thf('20', plain,
% 0.85/1.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.85/1.05         ((v1_relat_1 @ X18)
% 0.85/1.05          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.85/1.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.85/1.05  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.85/1.05  thf('22', plain,
% 0.85/1.05      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.05      inference('demod', [status(thm)], ['18', '21'])).
% 0.85/1.05  thf('23', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf(t3_subset, axiom,
% 0.85/1.05    (![A:$i,B:$i]:
% 0.85/1.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.85/1.05  thf('24', plain,
% 0.85/1.05      (![X5 : $i, X6 : $i]:
% 0.85/1.05         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.85/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.85/1.05  thf('25', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.85/1.05      inference('sup-', [status(thm)], ['23', '24'])).
% 0.85/1.05  thf(t12_xboole_1, axiom,
% 0.85/1.05    (![A:$i,B:$i]:
% 0.85/1.05     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.85/1.05  thf('26', plain,
% 0.85/1.05      (![X3 : $i, X4 : $i]:
% 0.85/1.05         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.85/1.05      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.85/1.05  thf('27', plain, (((k2_xboole_0 @ sk_D @ sk_A) = (sk_A))),
% 0.85/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.85/1.05  thf(t11_xboole_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.85/1.05  thf('28', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.05         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.85/1.05      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.85/1.05  thf('29', plain,
% 0.85/1.05      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_D @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['27', '28'])).
% 0.85/1.05  thf('30', plain,
% 0.85/1.05      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['22', '29'])).
% 0.85/1.05  thf(t163_funct_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.85/1.05       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.85/1.05           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.85/1.05         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.85/1.05  thf('31', plain,
% 0.85/1.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.85/1.05         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.85/1.05          | ~ (r1_tarski @ (k9_relat_1 @ X16 @ X15) @ X17)
% 0.85/1.05          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ X17))
% 0.85/1.05          | ~ (v1_funct_1 @ X16)
% 0.85/1.05          | ~ (v1_relat_1 @ X16))),
% 0.85/1.05      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.85/1.05  thf('32', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (((sk_B) = (k1_xboole_0))
% 0.85/1.05          | ~ (v1_relat_1 @ sk_C)
% 0.85/1.05          | ~ (v1_funct_1 @ sk_C)
% 0.85/1.05          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 0.85/1.05          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['30', '31'])).
% 0.85/1.05  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.85/1.05  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('35', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (((sk_B) = (k1_xboole_0))
% 0.85/1.05          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 0.85/1.05          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 0.85/1.05      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.85/1.05  thf('36', plain,
% 0.85/1.05      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 0.85/1.05         | ((sk_B) = (k1_xboole_0))))
% 0.85/1.05         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['7', '35'])).
% 0.85/1.05  thf('37', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.05  thf('38', plain,
% 0.85/1.05      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.85/1.05         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('split', [status(esa)], ['0'])).
% 0.85/1.05  thf('39', plain,
% 0.85/1.05      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.85/1.05         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['37', '38'])).
% 0.85/1.05  thf('40', plain,
% 0.85/1.05      ((((sk_B) = (k1_xboole_0)))
% 0.85/1.05         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.85/1.05             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['36', '39'])).
% 0.85/1.05  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('42', plain,
% 0.85/1.05      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.85/1.05         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.85/1.05             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['40', '41'])).
% 0.85/1.05  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.85/1.05  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('44', plain,
% 0.85/1.05      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.85/1.05       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.85/1.05      inference('demod', [status(thm)], ['42', '43'])).
% 0.85/1.05  thf('45', plain,
% 0.85/1.05      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.85/1.05       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.85/1.05      inference('split', [status(esa)], ['5'])).
% 0.85/1.05  thf(t145_funct_1, axiom,
% 0.85/1.05    (![A:$i,B:$i]:
% 0.85/1.05     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.85/1.05       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.85/1.05  thf('46', plain,
% 0.85/1.05      (![X13 : $i, X14 : $i]:
% 0.85/1.05         ((r1_tarski @ (k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X14)) @ X14)
% 0.85/1.05          | ~ (v1_funct_1 @ X13)
% 0.85/1.05          | ~ (v1_relat_1 @ X13))),
% 0.85/1.05      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.85/1.05  thf('47', plain,
% 0.85/1.05      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('split', [status(esa)], ['5'])).
% 0.85/1.05  thf(t156_relat_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( v1_relat_1 @ C ) =>
% 0.85/1.05       ( ( r1_tarski @ A @ B ) =>
% 0.85/1.05         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.85/1.05  thf('48', plain,
% 0.85/1.05      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.85/1.05         (~ (r1_tarski @ X8 @ X9)
% 0.85/1.05          | ~ (v1_relat_1 @ X10)
% 0.85/1.05          | (r1_tarski @ (k9_relat_1 @ X10 @ X8) @ (k9_relat_1 @ X10 @ X9)))),
% 0.85/1.05      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.85/1.05  thf('49', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.85/1.05            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.85/1.05           | ~ (v1_relat_1 @ X0)))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.05  thf('50', plain,
% 0.85/1.05      (![X3 : $i, X4 : $i]:
% 0.85/1.05         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.85/1.05      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.85/1.05  thf('51', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          (~ (v1_relat_1 @ X0)
% 0.85/1.05           | ((k2_xboole_0 @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.85/1.05               (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.85/1.05               = (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['49', '50'])).
% 0.85/1.05  thf('52', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.05  thf('53', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.05  thf('54', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          (~ (v1_relat_1 @ X0)
% 0.85/1.05           | ((k2_xboole_0 @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.85/1.05               (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.85/1.05               = (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)))))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.85/1.05  thf('55', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.05         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.85/1.05      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.85/1.05  thf('56', plain,
% 0.85/1.05      ((![X0 : $i, X1 : $i]:
% 0.85/1.05          (~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ X1)
% 0.85/1.05           | ~ (v1_relat_1 @ X0)
% 0.85/1.05           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['54', '55'])).
% 0.85/1.05  thf('57', plain,
% 0.85/1.05      (((~ (v1_relat_1 @ sk_C)
% 0.85/1.05         | ~ (v1_funct_1 @ sk_C)
% 0.85/1.05         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 0.85/1.05         | ~ (v1_relat_1 @ sk_C)))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['46', '56'])).
% 0.85/1.05  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.85/1.05  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.85/1.05  thf('61', plain,
% 0.85/1.05      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.85/1.05         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.85/1.05      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.85/1.05  thf('62', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.05  thf('63', plain,
% 0.85/1.05      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.85/1.05         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('split', [status(esa)], ['0'])).
% 0.85/1.05  thf('64', plain,
% 0.85/1.05      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.85/1.05         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['62', '63'])).
% 0.85/1.05  thf('65', plain,
% 0.85/1.05      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.85/1.05       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.85/1.05      inference('sup-', [status(thm)], ['61', '64'])).
% 0.85/1.05  thf('66', plain, ($false),
% 0.85/1.05      inference('sat_resolution*', [status(thm)], ['1', '44', '45', '65'])).
% 0.85/1.05  
% 0.85/1.05  % SZS output end Refutation
% 0.85/1.05  
% 0.85/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
