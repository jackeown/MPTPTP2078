%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vPsgNh4bxz

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:34 EST 2020

% Result     : Theorem 32.36s
% Output     : Refutation 32.36s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 156 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  908 (2676 expanded)
%              Number of equality atoms :   32 (  36 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k7_relset_1 @ X56 @ X57 @ X55 @ X58 )
        = ( k9_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( X68 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X68 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X68 ) ) )
      | ( ( k8_relset_1 @ X66 @ X68 @ X67 @ X68 )
        = X66 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('10',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( ( k8_relset_1 @ X63 @ X64 @ X65 @ X64 )
        = ( k1_relset_1 @ X63 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('16',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
    = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k1_relset_1 @ X53 @ X54 @ X52 )
        = ( k1_relat_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ X43 @ ( k1_relat_1 @ X44 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X44 @ X43 ) @ X45 )
      | ( r1_tarski @ X43 @ ( k10_relat_1 @ X44 @ X45 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v1_relat_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ sk_E ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ sk_D @ sk_A ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ sk_E ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( ( k8_relset_1 @ X60 @ X61 @ X59 @ X62 )
        = ( k10_relat_1 @ X59 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C_1 @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
      & ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
      & ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X41 @ ( k10_relat_1 @ X41 @ X42 ) ) @ X42 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('47',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X39 )
      | ( r1_tarski @ ( k9_relat_1 @ X39 @ X37 ) @ ( k9_relat_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('57',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vPsgNh4bxz
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 32.36/32.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.36/32.57  % Solved by: fo/fo7.sh
% 32.36/32.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.36/32.57  % done 61256 iterations in 32.110s
% 32.36/32.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.36/32.57  % SZS output start Refutation
% 32.36/32.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.36/32.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 32.36/32.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 32.36/32.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 32.36/32.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 32.36/32.57  thf(sk_A_type, type, sk_A: $i).
% 32.36/32.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.36/32.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.36/32.57  thf(sk_D_type, type, sk_D: $i).
% 32.36/32.57  thf(sk_E_type, type, sk_E: $i).
% 32.36/32.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.36/32.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.36/32.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 32.36/32.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.36/32.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 32.36/32.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.36/32.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 32.36/32.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 32.36/32.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 32.36/32.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.36/32.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 32.36/32.57  thf(t172_funct_2, conjecture,
% 32.36/32.57    (![A:$i]:
% 32.36/32.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 32.36/32.57       ( ![B:$i]:
% 32.36/32.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 32.36/32.57           ( ![C:$i]:
% 32.36/32.57             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.36/32.57                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.36/32.57               ( ![D:$i]:
% 32.36/32.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 32.36/32.57                   ( ![E:$i]:
% 32.36/32.57                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 32.36/32.57                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 32.36/32.57                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 32.36/32.57  thf(zf_stmt_0, negated_conjecture,
% 32.36/32.57    (~( ![A:$i]:
% 32.36/32.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 32.36/32.57          ( ![B:$i]:
% 32.36/32.57            ( ( ~( v1_xboole_0 @ B ) ) =>
% 32.36/32.57              ( ![C:$i]:
% 32.36/32.57                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.36/32.57                    ( m1_subset_1 @
% 32.36/32.57                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.36/32.57                  ( ![D:$i]:
% 32.36/32.57                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 32.36/32.57                      ( ![E:$i]:
% 32.36/32.57                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 32.36/32.57                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 32.36/32.57                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 32.36/32.57    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 32.36/32.57  thf('0', plain,
% 32.36/32.57      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))
% 32.36/32.57        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('1', plain,
% 32.36/32.57      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))) | 
% 32.36/32.57       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))),
% 32.36/32.57      inference('split', [status(esa)], ['0'])).
% 32.36/32.57  thf('2', plain,
% 32.36/32.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(redefinition_k7_relset_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i,D:$i]:
% 32.36/32.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.36/32.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 32.36/32.57  thf('3', plain,
% 32.36/32.57      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 32.36/32.57         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 32.36/32.57          | ((k7_relset_1 @ X56 @ X57 @ X55 @ X58) = (k9_relat_1 @ X55 @ X58)))),
% 32.36/32.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 32.36/32.57  thf('4', plain,
% 32.36/32.57      (![X0 : $i]:
% 32.36/32.57         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 32.36/32.57           = (k9_relat_1 @ sk_C_1 @ X0))),
% 32.36/32.57      inference('sup-', [status(thm)], ['2', '3'])).
% 32.36/32.57  thf('5', plain,
% 32.36/32.57      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))
% 32.36/32.57        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('6', plain,
% 32.36/32.57      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))
% 32.36/32.57         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('split', [status(esa)], ['5'])).
% 32.36/32.57  thf('7', plain,
% 32.36/32.57      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E))
% 32.36/32.57         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('sup+', [status(thm)], ['4', '6'])).
% 32.36/32.57  thf('8', plain,
% 32.36/32.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(t48_funct_2, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.36/32.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.36/32.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.36/32.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 32.36/32.57  thf('9', plain,
% 32.36/32.57      (![X66 : $i, X67 : $i, X68 : $i]:
% 32.36/32.57         (((X68) = (k1_xboole_0))
% 32.36/32.57          | ~ (v1_funct_1 @ X67)
% 32.36/32.57          | ~ (v1_funct_2 @ X67 @ X66 @ X68)
% 32.36/32.57          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X68)))
% 32.36/32.57          | ((k8_relset_1 @ X66 @ X68 @ X67 @ X68) = (X66)))),
% 32.36/32.57      inference('cnf', [status(esa)], [t48_funct_2])).
% 32.36/32.57  thf('10', plain,
% 32.36/32.57      ((((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) = (sk_A))
% 32.36/32.57        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 32.36/32.57        | ~ (v1_funct_1 @ sk_C_1)
% 32.36/32.57        | ((sk_B_1) = (k1_xboole_0)))),
% 32.36/32.57      inference('sup-', [status(thm)], ['8', '9'])).
% 32.36/32.57  thf('11', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('13', plain,
% 32.36/32.57      ((((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) = (sk_A))
% 32.36/32.57        | ((sk_B_1) = (k1_xboole_0)))),
% 32.36/32.57      inference('demod', [status(thm)], ['10', '11', '12'])).
% 32.36/32.57  thf('14', plain,
% 32.36/32.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(t38_relset_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.36/32.57       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 32.36/32.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 32.36/32.57  thf('15', plain,
% 32.36/32.57      (![X63 : $i, X64 : $i, X65 : $i]:
% 32.36/32.57         (((k8_relset_1 @ X63 @ X64 @ X65 @ X64)
% 32.36/32.57            = (k1_relset_1 @ X63 @ X64 @ X65))
% 32.36/32.57          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64))))),
% 32.36/32.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 32.36/32.57  thf('16', plain,
% 32.36/32.57      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1)
% 32.36/32.57         = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 32.36/32.57      inference('sup-', [status(thm)], ['14', '15'])).
% 32.36/32.57  thf('17', plain,
% 32.36/32.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(redefinition_k1_relset_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.36/32.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 32.36/32.57  thf('18', plain,
% 32.36/32.57      (![X52 : $i, X53 : $i, X54 : $i]:
% 32.36/32.57         (((k1_relset_1 @ X53 @ X54 @ X52) = (k1_relat_1 @ X52))
% 32.36/32.57          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 32.36/32.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 32.36/32.57  thf('19', plain,
% 32.36/32.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 32.36/32.57      inference('sup-', [status(thm)], ['17', '18'])).
% 32.36/32.57  thf('20', plain,
% 32.36/32.57      (((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_B_1) = (k1_relat_1 @ sk_C_1))),
% 32.36/32.57      inference('demod', [status(thm)], ['16', '19'])).
% 32.36/32.57  thf('21', plain,
% 32.36/32.57      ((((sk_A) = (k1_relat_1 @ sk_C_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 32.36/32.57      inference('sup+', [status(thm)], ['13', '20'])).
% 32.36/32.57  thf(t163_funct_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 32.36/32.57       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 32.36/32.57           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 32.36/32.57         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 32.36/32.57  thf('22', plain,
% 32.36/32.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 32.36/32.57         (~ (r1_tarski @ X43 @ (k1_relat_1 @ X44))
% 32.36/32.57          | ~ (r1_tarski @ (k9_relat_1 @ X44 @ X43) @ X45)
% 32.36/32.57          | (r1_tarski @ X43 @ (k10_relat_1 @ X44 @ X45))
% 32.36/32.57          | ~ (v1_funct_1 @ X44)
% 32.36/32.57          | ~ (v1_relat_1 @ X44))),
% 32.36/32.57      inference('cnf', [status(esa)], [t163_funct_1])).
% 32.36/32.57  thf('23', plain,
% 32.36/32.57      (![X0 : $i, X1 : $i]:
% 32.36/32.57         (~ (r1_tarski @ X0 @ sk_A)
% 32.36/32.57          | ((sk_B_1) = (k1_xboole_0))
% 32.36/32.57          | ~ (v1_relat_1 @ sk_C_1)
% 32.36/32.57          | ~ (v1_funct_1 @ sk_C_1)
% 32.36/32.57          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C_1 @ X1))
% 32.36/32.57          | ~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ X1))),
% 32.36/32.57      inference('sup-', [status(thm)], ['21', '22'])).
% 32.36/32.57  thf('24', plain,
% 32.36/32.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(cc1_relset_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.36/32.57       ( v1_relat_1 @ C ) ))).
% 32.36/32.57  thf('25', plain,
% 32.36/32.57      (![X46 : $i, X47 : $i, X48 : $i]:
% 32.36/32.57         ((v1_relat_1 @ X46)
% 32.36/32.57          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 32.36/32.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.36/32.57  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 32.36/32.57      inference('sup-', [status(thm)], ['24', '25'])).
% 32.36/32.57  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('28', plain,
% 32.36/32.57      (![X0 : $i, X1 : $i]:
% 32.36/32.57         (~ (r1_tarski @ X0 @ sk_A)
% 32.36/32.57          | ((sk_B_1) = (k1_xboole_0))
% 32.36/32.57          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C_1 @ X1))
% 32.36/32.57          | ~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ X1))),
% 32.36/32.57      inference('demod', [status(thm)], ['23', '26', '27'])).
% 32.36/32.57  thf('29', plain,
% 32.36/32.57      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ sk_E))
% 32.36/32.57         | ((sk_B_1) = (k1_xboole_0))
% 32.36/32.57         | ~ (r1_tarski @ sk_D @ sk_A)))
% 32.36/32.57         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('sup-', [status(thm)], ['7', '28'])).
% 32.36/32.57  thf('30', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(t3_subset, axiom,
% 32.36/32.57    (![A:$i,B:$i]:
% 32.36/32.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 32.36/32.57  thf('31', plain,
% 32.36/32.57      (![X27 : $i, X28 : $i]:
% 32.36/32.57         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 32.36/32.57      inference('cnf', [status(esa)], [t3_subset])).
% 32.36/32.57  thf('32', plain, ((r1_tarski @ sk_D @ sk_A)),
% 32.36/32.57      inference('sup-', [status(thm)], ['30', '31'])).
% 32.36/32.57  thf('33', plain,
% 32.36/32.57      ((((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ sk_E))
% 32.36/32.57         | ((sk_B_1) = (k1_xboole_0))))
% 32.36/32.57         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('demod', [status(thm)], ['29', '32'])).
% 32.36/32.57  thf('34', plain,
% 32.36/32.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf(redefinition_k8_relset_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i,D:$i]:
% 32.36/32.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.36/32.57       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 32.36/32.57  thf('35', plain,
% 32.36/32.57      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 32.36/32.57         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 32.36/32.57          | ((k8_relset_1 @ X60 @ X61 @ X59 @ X62) = (k10_relat_1 @ X59 @ X62)))),
% 32.36/32.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 32.36/32.57  thf('36', plain,
% 32.36/32.57      (![X0 : $i]:
% 32.36/32.57         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 32.36/32.57           = (k10_relat_1 @ sk_C_1 @ X0))),
% 32.36/32.57      inference('sup-', [status(thm)], ['34', '35'])).
% 32.36/32.57  thf('37', plain,
% 32.36/32.57      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)))
% 32.36/32.57         <= (~
% 32.36/32.57             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('split', [status(esa)], ['0'])).
% 32.36/32.57  thf('38', plain,
% 32.36/32.57      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C_1 @ sk_E)))
% 32.36/32.57         <= (~
% 32.36/32.57             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('sup-', [status(thm)], ['36', '37'])).
% 32.36/32.57  thf('39', plain,
% 32.36/32.57      ((((sk_B_1) = (k1_xboole_0)))
% 32.36/32.57         <= (~
% 32.36/32.57             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))) & 
% 32.36/32.57             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('sup-', [status(thm)], ['33', '38'])).
% 32.36/32.57  thf('40', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('41', plain,
% 32.36/32.57      ((~ (v1_xboole_0 @ k1_xboole_0))
% 32.36/32.57         <= (~
% 32.36/32.57             ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))) & 
% 32.36/32.57             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('sup-', [status(thm)], ['39', '40'])).
% 32.36/32.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 32.36/32.57  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 32.36/32.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 32.36/32.57  thf('43', plain,
% 32.36/32.57      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))) | 
% 32.36/32.57       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))),
% 32.36/32.57      inference('demod', [status(thm)], ['41', '42'])).
% 32.36/32.57  thf('44', plain,
% 32.36/32.57      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))) | 
% 32.36/32.57       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))),
% 32.36/32.57      inference('split', [status(esa)], ['5'])).
% 32.36/32.57  thf(t145_funct_1, axiom,
% 32.36/32.57    (![A:$i,B:$i]:
% 32.36/32.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.36/32.57       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 32.36/32.57  thf('45', plain,
% 32.36/32.57      (![X41 : $i, X42 : $i]:
% 32.36/32.57         ((r1_tarski @ (k9_relat_1 @ X41 @ (k10_relat_1 @ X41 @ X42)) @ X42)
% 32.36/32.57          | ~ (v1_funct_1 @ X41)
% 32.36/32.57          | ~ (v1_relat_1 @ X41))),
% 32.36/32.57      inference('cnf', [status(esa)], [t145_funct_1])).
% 32.36/32.57  thf('46', plain,
% 32.36/32.57      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)))
% 32.36/32.57         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('split', [status(esa)], ['5'])).
% 32.36/32.57  thf(t156_relat_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( v1_relat_1 @ C ) =>
% 32.36/32.57       ( ( r1_tarski @ A @ B ) =>
% 32.36/32.57         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 32.36/32.57  thf('47', plain,
% 32.36/32.57      (![X37 : $i, X38 : $i, X39 : $i]:
% 32.36/32.57         (~ (r1_tarski @ X37 @ X38)
% 32.36/32.57          | ~ (v1_relat_1 @ X39)
% 32.36/32.57          | (r1_tarski @ (k9_relat_1 @ X39 @ X37) @ (k9_relat_1 @ X39 @ X38)))),
% 32.36/32.57      inference('cnf', [status(esa)], [t156_relat_1])).
% 32.36/32.57  thf('48', plain,
% 32.36/32.57      ((![X0 : $i]:
% 32.36/32.57          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 32.36/32.57            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E)))
% 32.36/32.57           | ~ (v1_relat_1 @ X0)))
% 32.36/32.57         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('sup-', [status(thm)], ['46', '47'])).
% 32.36/32.57  thf('49', plain,
% 32.36/32.57      (![X0 : $i]:
% 32.36/32.57         ((k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 32.36/32.57           = (k10_relat_1 @ sk_C_1 @ X0))),
% 32.36/32.57      inference('sup-', [status(thm)], ['34', '35'])).
% 32.36/32.57  thf('50', plain,
% 32.36/32.57      ((![X0 : $i]:
% 32.36/32.57          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 32.36/32.57            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_E)))
% 32.36/32.57           | ~ (v1_relat_1 @ X0)))
% 32.36/32.57         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('demod', [status(thm)], ['48', '49'])).
% 32.36/32.57  thf(t1_xboole_1, axiom,
% 32.36/32.57    (![A:$i,B:$i,C:$i]:
% 32.36/32.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 32.36/32.57       ( r1_tarski @ A @ C ) ))).
% 32.36/32.57  thf('51', plain,
% 32.36/32.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 32.36/32.57         (~ (r1_tarski @ X14 @ X15)
% 32.36/32.57          | ~ (r1_tarski @ X15 @ X16)
% 32.36/32.57          | (r1_tarski @ X14 @ X16))),
% 32.36/32.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 32.36/32.57  thf('52', plain,
% 32.36/32.57      ((![X0 : $i, X1 : $i]:
% 32.36/32.57          (~ (v1_relat_1 @ X0)
% 32.36/32.57           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 32.36/32.57           | ~ (r1_tarski @ 
% 32.36/32.57                (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_E)) @ X1)))
% 32.36/32.57         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('sup-', [status(thm)], ['50', '51'])).
% 32.36/32.57  thf('53', plain,
% 32.36/32.57      (((~ (v1_relat_1 @ sk_C_1)
% 32.36/32.57         | ~ (v1_funct_1 @ sk_C_1)
% 32.36/32.57         | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E)
% 32.36/32.57         | ~ (v1_relat_1 @ sk_C_1)))
% 32.36/32.57         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('sup-', [status(thm)], ['45', '52'])).
% 32.36/32.57  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 32.36/32.57      inference('sup-', [status(thm)], ['24', '25'])).
% 32.36/32.57  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 32.36/32.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.36/32.57  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 32.36/32.57      inference('sup-', [status(thm)], ['24', '25'])).
% 32.36/32.57  thf('57', plain,
% 32.36/32.57      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E))
% 32.36/32.57         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))))),
% 32.36/32.57      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 32.36/32.57  thf('58', plain,
% 32.36/32.57      (![X0 : $i]:
% 32.36/32.57         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ X0)
% 32.36/32.57           = (k9_relat_1 @ sk_C_1 @ X0))),
% 32.36/32.57      inference('sup-', [status(thm)], ['2', '3'])).
% 32.36/32.57  thf('59', plain,
% 32.36/32.57      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))
% 32.36/32.57         <= (~
% 32.36/32.57             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('split', [status(esa)], ['0'])).
% 32.36/32.57  thf('60', plain,
% 32.36/32.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_D) @ sk_E))
% 32.36/32.57         <= (~
% 32.36/32.57             ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E)))),
% 32.36/32.57      inference('sup-', [status(thm)], ['58', '59'])).
% 32.36/32.57  thf('61', plain,
% 32.36/32.57      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E))) | 
% 32.36/32.57       ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_E))),
% 32.36/32.57      inference('sup-', [status(thm)], ['57', '60'])).
% 32.36/32.57  thf('62', plain, ($false),
% 32.36/32.57      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '61'])).
% 32.36/32.57  
% 32.36/32.57  % SZS output end Refutation
% 32.36/32.57  
% 32.36/32.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
