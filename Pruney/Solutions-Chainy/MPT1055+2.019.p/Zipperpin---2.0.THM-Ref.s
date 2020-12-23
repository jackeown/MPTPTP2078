%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N8dRu4ifv6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:36 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 225 expanded)
%              Number of leaves         :   40 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  883 (3571 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

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
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
   <= ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['9'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X12 @ X10 ) @ ( k9_relat_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_D ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('24',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['16','21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['6','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['5','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['9'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('35',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['9'])).

thf('37',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ),
    inference('sat_resolution*',[status(thm)],['6','30','36'])).

thf('38',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','50','53'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X16 @ X15 ) @ X17 )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['32','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N8dRu4ifv6
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 250 iterations in 0.522s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.76/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.99  thf(sk_E_type, type, sk_E: $i).
% 0.76/0.99  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.99  thf(t172_funct_2, conjecture,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.99           ( ![C:$i]:
% 0.76/0.99             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.99               ( ![D:$i]:
% 0.76/0.99                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.99                   ( ![E:$i]:
% 0.76/0.99                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.76/0.99                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.76/0.99                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.99    (~( ![A:$i]:
% 0.76/0.99        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.99          ( ![B:$i]:
% 0.76/0.99            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.99              ( ![C:$i]:
% 0.76/0.99                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.99                    ( m1_subset_1 @
% 0.76/0.99                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.99                  ( ![D:$i]:
% 0.76/0.99                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.99                      ( ![E:$i]:
% 0.76/0.99                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.76/0.99                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.76/0.99                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.76/0.99        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.76/0.99         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('2', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k8_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.76/0.99          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.76/0.99  thf('4', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('5', plain,
% 0.76/0.99      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.76/0.99         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('demod', [status(thm)], ['1', '4'])).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.76/0.99       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf(t145_funct_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.99       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.76/0.99  thf('7', plain,
% 0.76/0.99      (![X13 : $i, X14 : $i]:
% 0.76/0.99         ((r1_tarski @ (k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X14)) @ X14)
% 0.76/0.99          | ~ (v1_funct_1 @ X13)
% 0.76/0.99          | ~ (v1_relat_1 @ X13))),
% 0.76/0.99      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.76/0.99  thf('8', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf('9', plain,
% 0.76/0.99      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.76/0.99        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('10', plain,
% 0.76/0.99      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.76/0.99         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('split', [status(esa)], ['9'])).
% 0.76/0.99  thf(t156_relat_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( v1_relat_1 @ C ) =>
% 0.76/0.99       ( ( r1_tarski @ A @ B ) =>
% 0.76/0.99         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.76/0.99  thf('11', plain,
% 0.76/0.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.99         (~ (r1_tarski @ X10 @ X11)
% 0.76/0.99          | ~ (v1_relat_1 @ X12)
% 0.76/0.99          | (r1_tarski @ (k9_relat_1 @ X12 @ X10) @ (k9_relat_1 @ X12 @ X11)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.76/0.99  thf('12', plain,
% 0.76/0.99      ((![X0 : $i]:
% 0.76/0.99          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.76/0.99            (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.76/0.99           | ~ (v1_relat_1 @ X0)))
% 0.76/0.99         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/0.99  thf(t1_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.76/0.99       ( r1_tarski @ A @ C ) ))).
% 0.76/0.99  thf('13', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.99         (~ (r1_tarski @ X0 @ X1)
% 0.76/0.99          | ~ (r1_tarski @ X1 @ X2)
% 0.76/0.99          | (r1_tarski @ X0 @ X2))),
% 0.76/0.99      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.99  thf('14', plain,
% 0.76/0.99      ((![X0 : $i, X1 : $i]:
% 0.76/0.99          (~ (v1_relat_1 @ X0)
% 0.76/0.99           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 0.76/0.99           | ~ (r1_tarski @ 
% 0.76/0.99                (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)) @ 
% 0.76/0.99                X1)))
% 0.76/0.99         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      ((![X0 : $i, X1 : $i]:
% 0.76/0.99          (~ (r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_C @ sk_E)) @ X0)
% 0.76/0.99           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_D) @ X0)
% 0.76/0.99           | ~ (v1_relat_1 @ X1)))
% 0.76/0.99         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['8', '14'])).
% 0.76/0.99  thf('16', plain,
% 0.76/0.99      (((~ (v1_relat_1 @ sk_C)
% 0.76/0.99         | ~ (v1_funct_1 @ sk_C)
% 0.76/0.99         | ~ (v1_relat_1 @ sk_C)
% 0.76/0.99         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)))
% 0.76/0.99         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['7', '15'])).
% 0.76/0.99  thf('17', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(cc2_relat_1, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ( v1_relat_1 @ A ) =>
% 0.76/0.99       ( ![B:$i]:
% 0.76/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.99  thf('18', plain,
% 0.76/0.99      (![X6 : $i, X7 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.76/0.99          | (v1_relat_1 @ X6)
% 0.76/0.99          | ~ (v1_relat_1 @ X7))),
% 0.76/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.99  thf('19', plain,
% 0.76/0.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.99  thf(fc6_relat_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.76/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.99  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.99  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.99  thf('24', plain,
% 0.76/0.99      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.76/0.99         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.76/0.99      inference('demod', [status(thm)], ['16', '21', '22', '23'])).
% 0.76/0.99  thf('25', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k7_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.76/0.99  thf('26', plain,
% 0.76/0.99      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.76/0.99          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.76/0.99  thf('27', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.99  thf('28', plain,
% 0.76/0.99      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.76/0.99         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.76/0.99      inference('split', [status(esa)], ['0'])).
% 0.76/0.99  thf('29', plain,
% 0.76/0.99      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.76/0.99         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.99  thf('30', plain,
% 0.76/0.99      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 0.76/0.99       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['24', '29'])).
% 0.76/0.99  thf('31', plain,
% 0.76/0.99      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.76/0.99      inference('sat_resolution*', [status(thm)], ['6', '30'])).
% 0.76/0.99  thf('32', plain, (~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['5', '31'])).
% 0.76/0.99  thf('33', plain,
% 0.76/0.99      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.76/0.99         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.76/0.99      inference('split', [status(esa)], ['9'])).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      (![X0 : $i]:
% 0.76/0.99         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.99  thf('35', plain,
% 0.76/0.99      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.76/0.99         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.76/0.99      inference('demod', [status(thm)], ['33', '34'])).
% 0.76/0.99  thf('36', plain,
% 0.76/0.99      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 0.76/0.99       ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.76/0.99      inference('split', [status(esa)], ['9'])).
% 0.76/0.99  thf('37', plain,
% 0.76/0.99      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.76/0.99      inference('sat_resolution*', [status(thm)], ['6', '30', '36'])).
% 0.76/0.99  thf('38', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.76/0.99  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(d1_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_1, axiom,
% 0.76/0.99    (![C:$i,B:$i,A:$i]:
% 0.76/0.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.99  thf('40', plain,
% 0.76/0.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.76/0.99          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.76/0.99          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.99  thf('41', plain,
% 0.76/0.99      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.76/0.99        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.99  thf(zf_stmt_2, axiom,
% 0.76/0.99    (![B:$i,A:$i]:
% 0.76/0.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.99       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      (![X29 : $i, X30 : $i]:
% 0.76/0.99         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.99  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.76/0.99      inference('sup+', [status(thm)], ['42', '43'])).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_5, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.99  thf('46', plain,
% 0.76/0.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.76/0.99         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.76/0.99          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.76/0.99          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.99  thf('47', plain,
% 0.76/0.99      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['44', '47'])).
% 0.76/0.99  thf('49', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('50', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.76/0.99      inference('clc', [status(thm)], ['48', '49'])).
% 0.76/0.99  thf('51', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/0.99         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.76/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.76/0.99      inference('sup-', [status(thm)], ['51', '52'])).
% 0.76/0.99  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.76/0.99      inference('demod', [status(thm)], ['41', '50', '53'])).
% 0.76/0.99  thf(t163_funct_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.99       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.99           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.76/0.99         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.76/0.99  thf('55', plain,
% 0.76/0.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.99         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.76/0.99          | ~ (r1_tarski @ (k9_relat_1 @ X16 @ X15) @ X17)
% 0.76/0.99          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ X17))
% 0.76/0.99          | ~ (v1_funct_1 @ X16)
% 0.76/0.99          | ~ (v1_relat_1 @ X16))),
% 0.76/0.99      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.76/0.99  thf('56', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.99          | ~ (v1_relat_1 @ sk_C)
% 0.76/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.99          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 0.76/0.99          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['54', '55'])).
% 0.76/0.99  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.99      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.99  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('59', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.99          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 0.76/0.99          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 0.76/0.99      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 0.76/0.99        | ~ (r1_tarski @ sk_D @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['38', '59'])).
% 0.76/0.99  thf('61', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf(t3_subset, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.99  thf('62', plain,
% 0.76/0.99      (![X3 : $i, X4 : $i]:
% 0.76/0.99         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.99  thf('63', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.76/0.99      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/0.99  thf('64', plain, ((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 0.76/0.99      inference('demod', [status(thm)], ['60', '63'])).
% 0.76/0.99  thf('65', plain, ($false), inference('demod', [status(thm)], ['32', '64'])).
% 0.76/0.99  
% 0.76/0.99  % SZS output end Refutation
% 0.76/0.99  
% 0.76/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
