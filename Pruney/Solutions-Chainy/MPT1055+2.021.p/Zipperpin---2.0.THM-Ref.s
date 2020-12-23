%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CbHOMni8lh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:36 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 171 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  854 (2731 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X30 ) ) )
      | ( ( k8_relset_1 @ X28 @ X30 @ X29 @ X30 )
        = X28 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X18 @ X17 ) @ X19 )
      | ( r1_tarski @ X17 @ ( k10_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    inference(demod,[status(thm)],['21','22'])).

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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('48',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X12 @ X10 ) @ ( k9_relat_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_D ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('58',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CbHOMni8lh
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 552 iterations in 0.255s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.53/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.53/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(t172_funct_2, conjecture,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.53/0.71           ( ![C:$i]:
% 0.53/0.71             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.71                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.71               ( ![D:$i]:
% 0.53/0.71                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.71                   ( ![E:$i]:
% 0.53/0.71                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.53/0.71                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.53/0.71                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i]:
% 0.53/0.71        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.71          ( ![B:$i]:
% 0.53/0.71            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.53/0.71              ( ![C:$i]:
% 0.53/0.71                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.71                    ( m1_subset_1 @
% 0.53/0.71                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.71                  ( ![D:$i]:
% 0.53/0.71                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.71                      ( ![E:$i]:
% 0.53/0.71                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.53/0.71                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.53/0.71                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.53/0.71        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.53/0.71       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.53/0.71      inference('split', [status(esa)], ['0'])).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(redefinition_k7_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.53/0.71          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.53/0.71        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.53/0.71         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('split', [status(esa)], ['5'])).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.53/0.71         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['4', '6'])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t48_funct_2, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.71         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.71         (((X30) = (k1_xboole_0))
% 0.53/0.71          | ~ (v1_funct_1 @ X29)
% 0.53/0.71          | ~ (v1_funct_2 @ X29 @ X28 @ X30)
% 0.53/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X30)))
% 0.53/0.71          | ((k8_relset_1 @ X28 @ X30 @ X29 @ X30) = (X28)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) = (sk_A))
% 0.53/0.71        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.53/0.71        | ((sk_B) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(redefinition_k8_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.53/0.71          | ((k8_relset_1 @ X25 @ X26 @ X24 @ X27) = (k10_relat_1 @ X24 @ X27)))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('16', plain,
% 0.53/0.71      ((((k10_relat_1 @ sk_C @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['10', '13', '14', '15'])).
% 0.53/0.71  thf(t167_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      (![X13 : $i, X14 : $i]:
% 0.53/0.71         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 0.53/0.71          | ~ (v1_relat_1 @ X13))),
% 0.53/0.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.53/0.71  thf('18', plain,
% 0.53/0.71      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 0.53/0.71        | ((sk_B) = (k1_xboole_0))
% 0.53/0.71        | ~ (v1_relat_1 @ sk_C))),
% 0.53/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc2_relat_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (![X6 : $i, X7 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.53/0.71          | (v1_relat_1 @ X6)
% 0.53/0.71          | ~ (v1_relat_1 @ X7))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.53/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.71  thf(fc6_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.71  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['18', '23'])).
% 0.53/0.71  thf('25', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t3_subset, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.71  thf('26', plain,
% 0.53/0.71      (![X3 : $i, X4 : $i]:
% 0.53/0.71         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.71  thf('27', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.53/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.71  thf(t1_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.53/0.71       ( r1_tarski @ A @ C ) ))).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.71          | ~ (r1_tarski @ X1 @ X2)
% 0.53/0.71          | (r1_tarski @ X0 @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.71  thf('30', plain,
% 0.53/0.71      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['24', '29'])).
% 0.53/0.71  thf(t163_funct_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.71       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.53/0.71           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.53/0.71         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 0.53/0.71          | ~ (r1_tarski @ (k9_relat_1 @ X18 @ X17) @ X19)
% 0.53/0.71          | (r1_tarski @ X17 @ (k10_relat_1 @ X18 @ X19))
% 0.53/0.71          | ~ (v1_funct_1 @ X18)
% 0.53/0.71          | ~ (v1_relat_1 @ X18))),
% 0.53/0.71      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.53/0.71  thf('32', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((sk_B) = (k1_xboole_0))
% 0.53/0.71          | ~ (v1_relat_1 @ sk_C)
% 0.53/0.71          | ~ (v1_funct_1 @ sk_C)
% 0.53/0.71          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 0.53/0.71          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.71  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((sk_B) = (k1_xboole_0))
% 0.53/0.71          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 0.53/0.71          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 0.53/0.71      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.53/0.71  thf('36', plain,
% 0.53/0.71      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 0.53/0.71         | ((sk_B) = (k1_xboole_0))))
% 0.53/0.71         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['7', '35'])).
% 0.53/0.71  thf('37', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('38', plain,
% 0.53/0.71      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.53/0.71         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('split', [status(esa)], ['0'])).
% 0.53/0.71  thf('39', plain,
% 0.53/0.71      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.53/0.71         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.71  thf('40', plain,
% 0.53/0.71      ((((sk_B) = (k1_xboole_0)))
% 0.53/0.71         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.53/0.71             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['36', '39'])).
% 0.53/0.71  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('42', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.53/0.71         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.53/0.71             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.71  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('44', plain,
% 0.53/0.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.53/0.71       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.53/0.71      inference('demod', [status(thm)], ['42', '43'])).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.53/0.71       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.53/0.71      inference('split', [status(esa)], ['5'])).
% 0.53/0.71  thf(t145_funct_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.71       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.53/0.71  thf('46', plain,
% 0.53/0.71      (![X15 : $i, X16 : $i]:
% 0.53/0.71         ((r1_tarski @ (k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X16)) @ X16)
% 0.53/0.71          | ~ (v1_funct_1 @ X15)
% 0.53/0.71          | ~ (v1_relat_1 @ X15))),
% 0.53/0.71      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.53/0.71  thf('47', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('48', plain,
% 0.53/0.71      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.53/0.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('split', [status(esa)], ['5'])).
% 0.53/0.71  thf(t156_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ C ) =>
% 0.53/0.71       ( ( r1_tarski @ A @ B ) =>
% 0.53/0.71         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.71  thf('49', plain,
% 0.53/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X10 @ X11)
% 0.53/0.71          | ~ (v1_relat_1 @ X12)
% 0.53/0.71          | (r1_tarski @ (k9_relat_1 @ X12 @ X10) @ (k9_relat_1 @ X12 @ X11)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.53/0.71  thf('50', plain,
% 0.53/0.71      ((![X0 : $i]:
% 0.53/0.71          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.53/0.71            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.53/0.71           | ~ (v1_relat_1 @ X0)))
% 0.53/0.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.71  thf('51', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X0 @ X1)
% 0.53/0.71          | ~ (r1_tarski @ X1 @ X2)
% 0.53/0.71          | (r1_tarski @ X0 @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.53/0.71  thf('52', plain,
% 0.53/0.71      ((![X0 : $i, X1 : $i]:
% 0.53/0.71          (~ (v1_relat_1 @ X0)
% 0.53/0.71           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 0.53/0.71           | ~ (r1_tarski @ 
% 0.53/0.71                (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)) @ 
% 0.53/0.71                X1)))
% 0.53/0.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.53/0.71  thf('53', plain,
% 0.53/0.71      ((![X0 : $i, X1 : $i]:
% 0.53/0.71          (~ (r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_C @ sk_E)) @ X0)
% 0.53/0.71           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_D) @ X0)
% 0.53/0.71           | ~ (v1_relat_1 @ X1)))
% 0.53/0.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['47', '52'])).
% 0.53/0.71  thf('54', plain,
% 0.53/0.71      (((~ (v1_relat_1 @ sk_C)
% 0.53/0.71         | ~ (v1_funct_1 @ sk_C)
% 0.53/0.71         | ~ (v1_relat_1 @ sk_C)
% 0.53/0.71         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)))
% 0.53/0.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['46', '53'])).
% 0.53/0.71  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.53/0.71  thf('58', plain,
% 0.53/0.71      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.53/0.71         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.53/0.71      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.53/0.71  thf('59', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.71  thf('60', plain,
% 0.53/0.71      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.53/0.71         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('split', [status(esa)], ['0'])).
% 0.53/0.71  thf('61', plain,
% 0.53/0.71      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.53/0.71         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['59', '60'])).
% 0.53/0.71  thf('62', plain,
% 0.53/0.71      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.53/0.71       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.53/0.71      inference('sup-', [status(thm)], ['58', '61'])).
% 0.53/0.71  thf('63', plain, ($false),
% 0.53/0.71      inference('sat_resolution*', [status(thm)], ['1', '44', '45', '62'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
