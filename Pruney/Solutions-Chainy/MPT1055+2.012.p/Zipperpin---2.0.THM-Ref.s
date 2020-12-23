%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3cME70cjl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:35 EST 2020

% Result     : Theorem 8.49s
% Output     : Refutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 617 expanded)
%              Number of leaves         :   40 ( 199 expanded)
%              Depth                    :   24
%              Number of atoms          : 1471 (8530 expanded)
%              Number of equality atoms :   52 ( 114 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k7_relset_1 @ X56 @ X57 @ X55 @ X58 )
        = ( k9_relat_1 @ X55 @ X58 ) ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X41 @ ( k10_relat_1 @ X41 @ X42 ) ) @ X42 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('11',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( ( k8_relset_1 @ X60 @ X61 @ X59 @ X62 )
        = ( k10_relat_1 @ X59 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( r1_tarski @ ( k9_relat_1 @ X36 @ X34 ) @ ( k9_relat_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_D ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) )
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
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

thf('35',plain,(
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

thf('36',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X78 )
      | ~ ( v1_funct_2 @ X78 @ X77 @ X79 )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X77 @ X79 ) ) )
      | ( ( k8_relset_1 @ X77 @ X79 @ X78 @ X79 )
        = X77 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('37',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v5_relat_1 @ X46 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v5_relat_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X63 ) @ X64 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X63 ) @ X65 )
      | ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X78 )
      | ~ ( v1_funct_2 @ X78 @ X77 @ X79 )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X77 @ X79 ) ) )
      | ( ( k8_relset_1 @ X77 @ X79 @ X78 @ X79 )
        = X77 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('57',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( ( k8_relset_1 @ X60 @ X61 @ X59 @ X62 )
        = ( k10_relat_1 @ X59 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X80: $i,X81: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X80 ) @ X81 )
      | ( v1_funct_2 @ X80 @ ( k1_relat_1 @ X80 ) @ X81 )
      | ~ ( v1_funct_1 @ X80 )
      | ~ ( v1_relat_1 @ X80 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('73',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v5_relat_1 @ X46 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v5_relat_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('96',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('97',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v4_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('100',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('105',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v4_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','110'])).

thf('112',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('113',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('114',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('117',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,
    ( ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','120'])).

thf('122',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('123',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ X43 @ ( k1_relat_1 @ X44 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X44 @ X43 ) @ X45 )
      | ( r1_tarski @ X43 @ ( k10_relat_1 @ X44 @ X45 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','127'])).

thf('129',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['7'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('131',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['8','31'])).

thf('133',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['131','132'])).

thf('134',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['128','133'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['0','134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3cME70cjl
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.49/8.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.49/8.77  % Solved by: fo/fo7.sh
% 8.49/8.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.49/8.77  % done 8857 iterations in 8.306s
% 8.49/8.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.49/8.77  % SZS output start Refutation
% 8.49/8.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.49/8.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.49/8.77  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 8.49/8.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.49/8.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.49/8.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.49/8.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.49/8.77  thf(sk_A_type, type, sk_A: $i).
% 8.49/8.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.49/8.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.49/8.77  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 8.49/8.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.49/8.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.49/8.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.49/8.77  thf(sk_E_type, type, sk_E: $i).
% 8.49/8.77  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 8.49/8.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.49/8.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.49/8.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.49/8.77  thf(sk_C_type, type, sk_C: $i).
% 8.49/8.77  thf(sk_B_type, type, sk_B: $i).
% 8.49/8.77  thf(sk_D_type, type, sk_D: $i).
% 8.49/8.77  thf(t172_funct_2, conjecture,
% 8.49/8.77    (![A:$i]:
% 8.49/8.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.49/8.77       ( ![B:$i]:
% 8.49/8.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.49/8.77           ( ![C:$i]:
% 8.49/8.77             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.49/8.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.49/8.77               ( ![D:$i]:
% 8.49/8.77                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 8.49/8.77                   ( ![E:$i]:
% 8.49/8.77                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 8.49/8.77                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 8.49/8.77                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.49/8.77  thf(zf_stmt_0, negated_conjecture,
% 8.49/8.77    (~( ![A:$i]:
% 8.49/8.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.49/8.77          ( ![B:$i]:
% 8.49/8.77            ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.49/8.77              ( ![C:$i]:
% 8.49/8.77                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.49/8.77                    ( m1_subset_1 @
% 8.49/8.77                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.49/8.77                  ( ![D:$i]:
% 8.49/8.77                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 8.49/8.77                      ( ![E:$i]:
% 8.49/8.77                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 8.49/8.77                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 8.49/8.77                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 8.49/8.77    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 8.49/8.77  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf('1', plain,
% 8.49/8.77      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.49/8.77        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf('2', plain,
% 8.49/8.77      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 8.49/8.77         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 8.49/8.77      inference('split', [status(esa)], ['1'])).
% 8.49/8.77  thf('3', plain,
% 8.49/8.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf(redefinition_k7_relset_1, axiom,
% 8.49/8.77    (![A:$i,B:$i,C:$i,D:$i]:
% 8.49/8.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.49/8.77       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 8.49/8.77  thf('4', plain,
% 8.49/8.77      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 8.49/8.77         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 8.49/8.77          | ((k7_relset_1 @ X56 @ X57 @ X55 @ X58) = (k9_relat_1 @ X55 @ X58)))),
% 8.49/8.77      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 8.49/8.77  thf('5', plain,
% 8.49/8.77      (![X0 : $i]:
% 8.49/8.77         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 8.49/8.77      inference('sup-', [status(thm)], ['3', '4'])).
% 8.49/8.77  thf('6', plain,
% 8.49/8.77      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 8.49/8.77         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 8.49/8.77      inference('demod', [status(thm)], ['2', '5'])).
% 8.49/8.77  thf('7', plain,
% 8.49/8.77      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.49/8.77        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf('8', plain,
% 8.49/8.77      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 8.49/8.77       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 8.49/8.77      inference('split', [status(esa)], ['7'])).
% 8.49/8.77  thf(t145_funct_1, axiom,
% 8.49/8.77    (![A:$i,B:$i]:
% 8.49/8.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.49/8.77       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 8.49/8.77  thf('9', plain,
% 8.49/8.77      (![X41 : $i, X42 : $i]:
% 8.49/8.77         ((r1_tarski @ (k9_relat_1 @ X41 @ (k10_relat_1 @ X41 @ X42)) @ X42)
% 8.49/8.77          | ~ (v1_funct_1 @ X41)
% 8.49/8.77          | ~ (v1_relat_1 @ X41))),
% 8.49/8.77      inference('cnf', [status(esa)], [t145_funct_1])).
% 8.49/8.77  thf('10', plain,
% 8.49/8.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf(redefinition_k8_relset_1, axiom,
% 8.49/8.77    (![A:$i,B:$i,C:$i,D:$i]:
% 8.49/8.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.49/8.77       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 8.49/8.77  thf('11', plain,
% 8.49/8.77      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 8.49/8.77         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 8.49/8.77          | ((k8_relset_1 @ X60 @ X61 @ X59 @ X62) = (k10_relat_1 @ X59 @ X62)))),
% 8.49/8.77      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 8.49/8.77  thf('12', plain,
% 8.49/8.77      (![X0 : $i]:
% 8.49/8.77         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 8.49/8.77      inference('sup-', [status(thm)], ['10', '11'])).
% 8.49/8.77  thf('13', plain,
% 8.49/8.77      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 8.49/8.77         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.49/8.77      inference('split', [status(esa)], ['1'])).
% 8.49/8.77  thf(t156_relat_1, axiom,
% 8.49/8.77    (![A:$i,B:$i,C:$i]:
% 8.49/8.77     ( ( v1_relat_1 @ C ) =>
% 8.49/8.77       ( ( r1_tarski @ A @ B ) =>
% 8.49/8.77         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 8.49/8.77  thf('14', plain,
% 8.49/8.77      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.49/8.77         (~ (r1_tarski @ X34 @ X35)
% 8.49/8.77          | ~ (v1_relat_1 @ X36)
% 8.49/8.77          | (r1_tarski @ (k9_relat_1 @ X36 @ X34) @ (k9_relat_1 @ X36 @ X35)))),
% 8.49/8.77      inference('cnf', [status(esa)], [t156_relat_1])).
% 8.49/8.77  thf('15', plain,
% 8.49/8.77      ((![X0 : $i]:
% 8.49/8.77          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 8.49/8.77            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 8.49/8.77           | ~ (v1_relat_1 @ X0)))
% 8.49/8.77         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.49/8.77      inference('sup-', [status(thm)], ['13', '14'])).
% 8.49/8.77  thf(t1_xboole_1, axiom,
% 8.49/8.77    (![A:$i,B:$i,C:$i]:
% 8.49/8.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.49/8.77       ( r1_tarski @ A @ C ) ))).
% 8.49/8.77  thf('16', plain,
% 8.49/8.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.49/8.77         (~ (r1_tarski @ X3 @ X4)
% 8.49/8.77          | ~ (r1_tarski @ X4 @ X5)
% 8.49/8.77          | (r1_tarski @ X3 @ X5))),
% 8.49/8.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.49/8.77  thf('17', plain,
% 8.49/8.77      ((![X0 : $i, X1 : $i]:
% 8.49/8.77          (~ (v1_relat_1 @ X0)
% 8.49/8.77           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 8.49/8.77           | ~ (r1_tarski @ 
% 8.49/8.77                (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)) @ 
% 8.49/8.77                X1)))
% 8.49/8.77         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.49/8.77      inference('sup-', [status(thm)], ['15', '16'])).
% 8.49/8.77  thf('18', plain,
% 8.49/8.77      ((![X0 : $i, X1 : $i]:
% 8.49/8.77          (~ (r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_C @ sk_E)) @ X0)
% 8.49/8.77           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_D) @ X0)
% 8.49/8.77           | ~ (v1_relat_1 @ X1)))
% 8.49/8.77         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.49/8.77      inference('sup-', [status(thm)], ['12', '17'])).
% 8.49/8.77  thf('19', plain,
% 8.49/8.77      (((~ (v1_relat_1 @ sk_C)
% 8.49/8.77         | ~ (v1_funct_1 @ sk_C)
% 8.49/8.77         | ~ (v1_relat_1 @ sk_C)
% 8.49/8.77         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)))
% 8.49/8.77         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.49/8.77      inference('sup-', [status(thm)], ['9', '18'])).
% 8.49/8.77  thf('20', plain,
% 8.49/8.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf(cc2_relat_1, axiom,
% 8.49/8.77    (![A:$i]:
% 8.49/8.77     ( ( v1_relat_1 @ A ) =>
% 8.49/8.77       ( ![B:$i]:
% 8.49/8.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.49/8.77  thf('21', plain,
% 8.49/8.77      (![X22 : $i, X23 : $i]:
% 8.49/8.77         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 8.49/8.77          | (v1_relat_1 @ X22)
% 8.49/8.77          | ~ (v1_relat_1 @ X23))),
% 8.49/8.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.49/8.77  thf('22', plain,
% 8.49/8.77      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 8.49/8.77      inference('sup-', [status(thm)], ['20', '21'])).
% 8.49/8.77  thf(fc6_relat_1, axiom,
% 8.49/8.77    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.49/8.77  thf('23', plain,
% 8.49/8.77      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 8.49/8.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.49/8.77  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 8.49/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.49/8.77  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 8.49/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.49/8.77  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 8.49/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.49/8.77  thf('27', plain,
% 8.49/8.77      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 8.49/8.77         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.49/8.77      inference('demod', [status(thm)], ['19', '24', '25', '26'])).
% 8.49/8.77  thf('28', plain,
% 8.49/8.77      (![X0 : $i]:
% 8.49/8.77         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 8.49/8.77      inference('sup-', [status(thm)], ['3', '4'])).
% 8.49/8.77  thf('29', plain,
% 8.49/8.77      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 8.49/8.77         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 8.49/8.77      inference('split', [status(esa)], ['7'])).
% 8.49/8.77  thf('30', plain,
% 8.49/8.77      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 8.49/8.77         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 8.49/8.77      inference('sup-', [status(thm)], ['28', '29'])).
% 8.59/8.77  thf('31', plain,
% 8.59/8.77      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 8.59/8.77       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['27', '30'])).
% 8.59/8.77  thf('32', plain,
% 8.59/8.77      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 8.59/8.77       ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 8.59/8.77      inference('split', [status(esa)], ['1'])).
% 8.59/8.77  thf('33', plain,
% 8.59/8.77      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 8.59/8.77      inference('sat_resolution*', [status(thm)], ['8', '31', '32'])).
% 8.59/8.77  thf('34', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 8.59/8.77      inference('simpl_trail', [status(thm)], ['6', '33'])).
% 8.59/8.77  thf('35', plain,
% 8.59/8.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf(t48_funct_2, axiom,
% 8.59/8.77    (![A:$i,B:$i,C:$i]:
% 8.59/8.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.59/8.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.59/8.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.59/8.77         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 8.59/8.77  thf('36', plain,
% 8.59/8.77      (![X77 : $i, X78 : $i, X79 : $i]:
% 8.59/8.77         (((X79) = (k1_xboole_0))
% 8.59/8.77          | ~ (v1_funct_1 @ X78)
% 8.59/8.77          | ~ (v1_funct_2 @ X78 @ X77 @ X79)
% 8.59/8.77          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X77 @ X79)))
% 8.59/8.77          | ((k8_relset_1 @ X77 @ X79 @ X78 @ X79) = (X77)))),
% 8.59/8.77      inference('cnf', [status(esa)], [t48_funct_2])).
% 8.59/8.77  thf('37', plain,
% 8.59/8.77      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) = (sk_A))
% 8.59/8.77        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 8.59/8.77        | ~ (v1_funct_1 @ sk_C)
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['35', '36'])).
% 8.59/8.77  thf('38', plain,
% 8.59/8.77      (![X0 : $i]:
% 8.59/8.77         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['10', '11'])).
% 8.59/8.77  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('41', plain,
% 8.59/8.77      ((((k10_relat_1 @ sk_C @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 8.59/8.77  thf('42', plain,
% 8.59/8.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf(cc2_relset_1, axiom,
% 8.59/8.77    (![A:$i,B:$i,C:$i]:
% 8.59/8.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.59/8.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.59/8.77  thf('43', plain,
% 8.59/8.77      (![X46 : $i, X47 : $i, X48 : $i]:
% 8.59/8.77         ((v5_relat_1 @ X46 @ X48)
% 8.59/8.77          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 8.59/8.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.59/8.77  thf('44', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 8.59/8.77      inference('sup-', [status(thm)], ['42', '43'])).
% 8.59/8.77  thf(d19_relat_1, axiom,
% 8.59/8.77    (![A:$i,B:$i]:
% 8.59/8.77     ( ( v1_relat_1 @ B ) =>
% 8.59/8.77       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.59/8.77  thf('45', plain,
% 8.59/8.77      (![X26 : $i, X27 : $i]:
% 8.59/8.77         (~ (v5_relat_1 @ X26 @ X27)
% 8.59/8.77          | (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 8.59/8.77          | ~ (v1_relat_1 @ X26))),
% 8.59/8.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.59/8.77  thf('46', plain,
% 8.59/8.77      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 8.59/8.77      inference('sup-', [status(thm)], ['44', '45'])).
% 8.59/8.77  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 8.59/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.59/8.77  thf('48', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 8.59/8.77      inference('demod', [status(thm)], ['46', '47'])).
% 8.59/8.77  thf(d10_xboole_0, axiom,
% 8.59/8.77    (![A:$i,B:$i]:
% 8.59/8.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.59/8.77  thf('49', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.59/8.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.59/8.77  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.59/8.77      inference('simplify', [status(thm)], ['49'])).
% 8.59/8.77  thf(t11_relset_1, axiom,
% 8.59/8.77    (![A:$i,B:$i,C:$i]:
% 8.59/8.77     ( ( v1_relat_1 @ C ) =>
% 8.59/8.77       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 8.59/8.77           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 8.59/8.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 8.59/8.77  thf('51', plain,
% 8.59/8.77      (![X63 : $i, X64 : $i, X65 : $i]:
% 8.59/8.77         (~ (r1_tarski @ (k1_relat_1 @ X63) @ X64)
% 8.59/8.77          | ~ (r1_tarski @ (k2_relat_1 @ X63) @ X65)
% 8.59/8.77          | (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 8.59/8.77          | ~ (v1_relat_1 @ X63))),
% 8.59/8.77      inference('cnf', [status(esa)], [t11_relset_1])).
% 8.59/8.77  thf('52', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (~ (v1_relat_1 @ X0)
% 8.59/8.77          | (m1_subset_1 @ X0 @ 
% 8.59/8.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 8.59/8.77          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 8.59/8.77      inference('sup-', [status(thm)], ['50', '51'])).
% 8.59/8.77  thf('53', plain,
% 8.59/8.77      (((m1_subset_1 @ sk_C @ 
% 8.59/8.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 8.59/8.77        | ~ (v1_relat_1 @ sk_C))),
% 8.59/8.77      inference('sup-', [status(thm)], ['48', '52'])).
% 8.59/8.77  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 8.59/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.59/8.77  thf('55', plain,
% 8.59/8.77      ((m1_subset_1 @ sk_C @ 
% 8.59/8.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 8.59/8.77      inference('demod', [status(thm)], ['53', '54'])).
% 8.59/8.77  thf('56', plain,
% 8.59/8.77      (![X77 : $i, X78 : $i, X79 : $i]:
% 8.59/8.77         (((X79) = (k1_xboole_0))
% 8.59/8.77          | ~ (v1_funct_1 @ X78)
% 8.59/8.77          | ~ (v1_funct_2 @ X78 @ X77 @ X79)
% 8.59/8.77          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X77 @ X79)))
% 8.59/8.77          | ((k8_relset_1 @ X77 @ X79 @ X78 @ X79) = (X77)))),
% 8.59/8.77      inference('cnf', [status(esa)], [t48_funct_2])).
% 8.59/8.77  thf('57', plain,
% 8.59/8.77      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ sk_B)
% 8.59/8.77          = (k1_relat_1 @ sk_C))
% 8.59/8.77        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 8.59/8.77        | ~ (v1_funct_1 @ sk_C)
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['55', '56'])).
% 8.59/8.77  thf('58', plain,
% 8.59/8.77      ((m1_subset_1 @ sk_C @ 
% 8.59/8.77        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 8.59/8.77      inference('demod', [status(thm)], ['53', '54'])).
% 8.59/8.77  thf('59', plain,
% 8.59/8.77      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 8.59/8.77         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 8.59/8.77          | ((k8_relset_1 @ X60 @ X61 @ X59 @ X62) = (k10_relat_1 @ X59 @ X62)))),
% 8.59/8.77      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 8.59/8.77  thf('60', plain,
% 8.59/8.77      (![X0 : $i]:
% 8.59/8.77         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ X0)
% 8.59/8.77           = (k10_relat_1 @ sk_C @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['58', '59'])).
% 8.59/8.77  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('62', plain,
% 8.59/8.77      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 8.59/8.77        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('demod', [status(thm)], ['57', '60', '61'])).
% 8.59/8.77  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 8.59/8.77      inference('demod', [status(thm)], ['46', '47'])).
% 8.59/8.77  thf(t4_funct_2, axiom,
% 8.59/8.77    (![A:$i,B:$i]:
% 8.59/8.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.59/8.77       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 8.59/8.77         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 8.59/8.77           ( m1_subset_1 @
% 8.59/8.77             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 8.59/8.77  thf('64', plain,
% 8.59/8.77      (![X80 : $i, X81 : $i]:
% 8.59/8.77         (~ (r1_tarski @ (k2_relat_1 @ X80) @ X81)
% 8.59/8.77          | (v1_funct_2 @ X80 @ (k1_relat_1 @ X80) @ X81)
% 8.59/8.77          | ~ (v1_funct_1 @ X80)
% 8.59/8.77          | ~ (v1_relat_1 @ X80))),
% 8.59/8.77      inference('cnf', [status(esa)], [t4_funct_2])).
% 8.59/8.77  thf('65', plain,
% 8.59/8.77      ((~ (v1_relat_1 @ sk_C)
% 8.59/8.77        | ~ (v1_funct_1 @ sk_C)
% 8.59/8.77        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B))),
% 8.59/8.77      inference('sup-', [status(thm)], ['63', '64'])).
% 8.59/8.77  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 8.59/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.59/8.77  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('68', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 8.59/8.77      inference('demod', [status(thm)], ['65', '66', '67'])).
% 8.59/8.77  thf('69', plain,
% 8.59/8.77      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('demod', [status(thm)], ['62', '68'])).
% 8.59/8.77  thf('70', plain,
% 8.59/8.77      ((((sk_A) = (k1_relat_1 @ sk_C))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('sup+', [status(thm)], ['41', '69'])).
% 8.59/8.77  thf('71', plain,
% 8.59/8.77      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.59/8.77      inference('simplify', [status(thm)], ['70'])).
% 8.59/8.77  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.59/8.77      inference('simplify', [status(thm)], ['49'])).
% 8.59/8.77  thf(t3_subset, axiom,
% 8.59/8.77    (![A:$i,B:$i]:
% 8.59/8.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.59/8.77  thf('73', plain,
% 8.59/8.77      (![X16 : $i, X18 : $i]:
% 8.59/8.77         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 8.59/8.77      inference('cnf', [status(esa)], [t3_subset])).
% 8.59/8.77  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['72', '73'])).
% 8.59/8.77  thf('75', plain,
% 8.59/8.77      (![X46 : $i, X47 : $i, X48 : $i]:
% 8.59/8.77         ((v5_relat_1 @ X46 @ X48)
% 8.59/8.77          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 8.59/8.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.59/8.77  thf('76', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 8.59/8.77      inference('sup-', [status(thm)], ['74', '75'])).
% 8.59/8.77  thf('77', plain,
% 8.59/8.77      (![X26 : $i, X27 : $i]:
% 8.59/8.77         (~ (v5_relat_1 @ X26 @ X27)
% 8.59/8.77          | (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 8.59/8.77          | ~ (v1_relat_1 @ X26))),
% 8.59/8.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.59/8.77  thf('78', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 8.59/8.77          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['76', '77'])).
% 8.59/8.77  thf('79', plain,
% 8.59/8.77      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 8.59/8.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.59/8.77  thf('80', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 8.59/8.77      inference('demod', [status(thm)], ['78', '79'])).
% 8.59/8.77  thf('81', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (~ (v1_relat_1 @ X0)
% 8.59/8.77          | (m1_subset_1 @ X0 @ 
% 8.59/8.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 8.59/8.77          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 8.59/8.77      inference('sup-', [status(thm)], ['50', '51'])).
% 8.59/8.77  thf('82', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 8.59/8.77           (k1_zfmisc_1 @ 
% 8.59/8.77            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))
% 8.59/8.77          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['80', '81'])).
% 8.59/8.77  thf('83', plain,
% 8.59/8.77      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 8.59/8.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.59/8.77  thf('84', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 8.59/8.77          (k1_zfmisc_1 @ 
% 8.59/8.77           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))),
% 8.59/8.77      inference('demod', [status(thm)], ['82', '83'])).
% 8.59/8.77  thf('85', plain,
% 8.59/8.77      (![X16 : $i, X17 : $i]:
% 8.59/8.77         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 8.59/8.77      inference('cnf', [status(esa)], [t3_subset])).
% 8.59/8.77  thf('86', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 8.59/8.77          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['84', '85'])).
% 8.59/8.77  thf('87', plain,
% 8.59/8.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('88', plain,
% 8.59/8.77      (![X16 : $i, X17 : $i]:
% 8.59/8.77         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 8.59/8.77      inference('cnf', [status(esa)], [t3_subset])).
% 8.59/8.77  thf('89', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 8.59/8.77      inference('sup-', [status(thm)], ['87', '88'])).
% 8.59/8.77  thf('90', plain,
% 8.59/8.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.59/8.77         (~ (r1_tarski @ X3 @ X4)
% 8.59/8.77          | ~ (r1_tarski @ X4 @ X5)
% 8.59/8.77          | (r1_tarski @ X3 @ X5))),
% 8.59/8.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.59/8.77  thf('91', plain,
% 8.59/8.77      (![X0 : $i]:
% 8.59/8.77         ((r1_tarski @ sk_C @ X0)
% 8.59/8.77          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['89', '90'])).
% 8.59/8.77  thf('92', plain,
% 8.59/8.77      ((r1_tarski @ sk_C @ 
% 8.59/8.77        (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_B))),
% 8.59/8.77      inference('sup-', [status(thm)], ['86', '91'])).
% 8.59/8.77  thf('93', plain,
% 8.59/8.77      (![X16 : $i, X18 : $i]:
% 8.59/8.77         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 8.59/8.77      inference('cnf', [status(esa)], [t3_subset])).
% 8.59/8.77  thf('94', plain,
% 8.59/8.77      ((m1_subset_1 @ sk_C @ 
% 8.59/8.77        (k1_zfmisc_1 @ 
% 8.59/8.77         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_B)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['92', '93'])).
% 8.59/8.77  thf('95', plain,
% 8.59/8.77      (![X46 : $i, X47 : $i, X48 : $i]:
% 8.59/8.77         ((v4_relat_1 @ X46 @ X47)
% 8.59/8.77          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 8.59/8.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.59/8.77  thf('96', plain,
% 8.59/8.77      ((v4_relat_1 @ sk_C @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['94', '95'])).
% 8.59/8.77  thf(d18_relat_1, axiom,
% 8.59/8.77    (![A:$i,B:$i]:
% 8.59/8.77     ( ( v1_relat_1 @ B ) =>
% 8.59/8.77       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.59/8.77  thf('97', plain,
% 8.59/8.77      (![X24 : $i, X25 : $i]:
% 8.59/8.77         (~ (v4_relat_1 @ X24 @ X25)
% 8.59/8.77          | (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 8.59/8.77          | ~ (v1_relat_1 @ X24))),
% 8.59/8.77      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.59/8.77  thf('98', plain,
% 8.59/8.77      ((~ (v1_relat_1 @ sk_C)
% 8.59/8.77        | (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 8.59/8.77           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 8.59/8.77      inference('sup-', [status(thm)], ['96', '97'])).
% 8.59/8.77  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 8.59/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.59/8.77  thf('100', plain,
% 8.59/8.77      ((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 8.59/8.77        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.59/8.77      inference('demod', [status(thm)], ['98', '99'])).
% 8.59/8.77  thf('101', plain,
% 8.59/8.77      (![X0 : $i, X2 : $i]:
% 8.59/8.77         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.59/8.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.59/8.77  thf('102', plain,
% 8.59/8.77      ((~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ 
% 8.59/8.77           (k1_relat_1 @ sk_C))
% 8.59/8.77        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_C)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['100', '101'])).
% 8.59/8.77  thf('103', plain,
% 8.59/8.77      ((~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A)
% 8.59/8.77        | ((sk_B) = (k1_xboole_0))
% 8.59/8.77        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_C)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['71', '102'])).
% 8.59/8.77  thf('104', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['72', '73'])).
% 8.59/8.77  thf('105', plain,
% 8.59/8.77      (![X46 : $i, X47 : $i, X48 : $i]:
% 8.59/8.77         ((v4_relat_1 @ X46 @ X47)
% 8.59/8.77          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 8.59/8.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.59/8.77  thf('106', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 8.59/8.77      inference('sup-', [status(thm)], ['104', '105'])).
% 8.59/8.77  thf('107', plain,
% 8.59/8.77      (![X24 : $i, X25 : $i]:
% 8.59/8.77         (~ (v4_relat_1 @ X24 @ X25)
% 8.59/8.77          | (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 8.59/8.77          | ~ (v1_relat_1 @ X24))),
% 8.59/8.77      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.59/8.77  thf('108', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 8.59/8.77          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['106', '107'])).
% 8.59/8.77  thf('109', plain,
% 8.59/8.77      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 8.59/8.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.59/8.77  thf('110', plain,
% 8.59/8.77      (![X0 : $i, X1 : $i]:
% 8.59/8.77         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 8.59/8.77      inference('demod', [status(thm)], ['108', '109'])).
% 8.59/8.77  thf('111', plain,
% 8.59/8.77      ((((sk_B) = (k1_xboole_0))
% 8.59/8.77        | ((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_C)))),
% 8.59/8.77      inference('demod', [status(thm)], ['103', '110'])).
% 8.59/8.77  thf('112', plain,
% 8.59/8.77      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 8.59/8.77      inference('simplify', [status(thm)], ['70'])).
% 8.59/8.77  thf('113', plain,
% 8.59/8.77      ((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 8.59/8.77        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.59/8.77      inference('demod', [status(thm)], ['98', '99'])).
% 8.59/8.77  thf('114', plain,
% 8.59/8.77      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('sup+', [status(thm)], ['112', '113'])).
% 8.59/8.77  thf('115', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('116', plain,
% 8.59/8.77      (![X16 : $i, X17 : $i]:
% 8.59/8.77         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 8.59/8.77      inference('cnf', [status(esa)], [t3_subset])).
% 8.59/8.77  thf('117', plain, ((r1_tarski @ sk_D @ sk_A)),
% 8.59/8.77      inference('sup-', [status(thm)], ['115', '116'])).
% 8.59/8.77  thf('118', plain,
% 8.59/8.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.59/8.77         (~ (r1_tarski @ X3 @ X4)
% 8.59/8.77          | ~ (r1_tarski @ X4 @ X5)
% 8.59/8.77          | (r1_tarski @ X3 @ X5))),
% 8.59/8.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.59/8.77  thf('119', plain,
% 8.59/8.77      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['117', '118'])).
% 8.59/8.77  thf('120', plain,
% 8.59/8.77      ((((sk_B) = (k1_xboole_0))
% 8.59/8.77        | (r1_tarski @ sk_D @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 8.59/8.77      inference('sup-', [status(thm)], ['114', '119'])).
% 8.59/8.77  thf('121', plain,
% 8.59/8.77      (((r1_tarski @ sk_D @ (k1_relat_1 @ sk_C))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('sup+', [status(thm)], ['111', '120'])).
% 8.59/8.77  thf('122', plain,
% 8.59/8.77      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_D @ (k1_relat_1 @ sk_C)))),
% 8.59/8.77      inference('simplify', [status(thm)], ['121'])).
% 8.59/8.77  thf(t163_funct_1, axiom,
% 8.59/8.77    (![A:$i,B:$i,C:$i]:
% 8.59/8.77     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.59/8.77       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 8.59/8.77           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 8.59/8.77         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 8.59/8.77  thf('123', plain,
% 8.59/8.77      (![X43 : $i, X44 : $i, X45 : $i]:
% 8.59/8.77         (~ (r1_tarski @ X43 @ (k1_relat_1 @ X44))
% 8.59/8.77          | ~ (r1_tarski @ (k9_relat_1 @ X44 @ X43) @ X45)
% 8.59/8.77          | (r1_tarski @ X43 @ (k10_relat_1 @ X44 @ X45))
% 8.59/8.77          | ~ (v1_funct_1 @ X44)
% 8.59/8.77          | ~ (v1_relat_1 @ X44))),
% 8.59/8.77      inference('cnf', [status(esa)], [t163_funct_1])).
% 8.59/8.77  thf('124', plain,
% 8.59/8.77      (![X0 : $i]:
% 8.59/8.77         (((sk_B) = (k1_xboole_0))
% 8.59/8.77          | ~ (v1_relat_1 @ sk_C)
% 8.59/8.77          | ~ (v1_funct_1 @ sk_C)
% 8.59/8.77          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 8.59/8.77          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['122', '123'])).
% 8.59/8.77  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 8.59/8.77      inference('demod', [status(thm)], ['22', '23'])).
% 8.59/8.77  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 8.59/8.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.59/8.77  thf('127', plain,
% 8.59/8.77      (![X0 : $i]:
% 8.59/8.77         (((sk_B) = (k1_xboole_0))
% 8.59/8.77          | (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ X0))
% 8.59/8.77          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ X0))),
% 8.59/8.77      inference('demod', [status(thm)], ['124', '125', '126'])).
% 8.59/8.77  thf('128', plain,
% 8.59/8.77      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 8.59/8.77        | ((sk_B) = (k1_xboole_0)))),
% 8.59/8.77      inference('sup-', [status(thm)], ['34', '127'])).
% 8.59/8.77  thf('129', plain,
% 8.59/8.77      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 8.59/8.77         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.59/8.77      inference('split', [status(esa)], ['7'])).
% 8.59/8.77  thf('130', plain,
% 8.59/8.77      (![X0 : $i]:
% 8.59/8.77         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 8.59/8.77      inference('sup-', [status(thm)], ['10', '11'])).
% 8.59/8.77  thf('131', plain,
% 8.59/8.77      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 8.59/8.77         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 8.59/8.77      inference('demod', [status(thm)], ['129', '130'])).
% 8.59/8.77  thf('132', plain,
% 8.59/8.77      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 8.59/8.77      inference('sat_resolution*', [status(thm)], ['8', '31'])).
% 8.59/8.77  thf('133', plain, (~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 8.59/8.77      inference('simpl_trail', [status(thm)], ['131', '132'])).
% 8.59/8.77  thf('134', plain, (((sk_B) = (k1_xboole_0))),
% 8.59/8.77      inference('clc', [status(thm)], ['128', '133'])).
% 8.59/8.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 8.59/8.77  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.59/8.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.59/8.77  thf('136', plain, ($false),
% 8.59/8.77      inference('demod', [status(thm)], ['0', '134', '135'])).
% 8.59/8.77  
% 8.59/8.77  % SZS output end Refutation
% 8.59/8.77  
% 8.59/8.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
