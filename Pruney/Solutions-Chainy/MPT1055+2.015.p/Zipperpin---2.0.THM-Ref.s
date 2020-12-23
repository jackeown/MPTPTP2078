%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.htE7lTi6zS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:36 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 235 expanded)
%              Number of leaves         :   41 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  937 (3679 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k8_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k10_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('8',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X13 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ ( k9_relat_1 @ X0 @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

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

thf('18',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_D ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_E ) ) @ X1 ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('28',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['20','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sat_resolution*',[status(thm)],['6','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['5','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(split,[status(esa)],['8'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
    | ( r1_tarski @ sk_D @ ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['8'])).

thf('41',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ),
    inference('sat_resolution*',[status(thm)],['6','34','40'])).

thf('42',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','54','57'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X20 @ X19 ) @ X21 )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_C @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) )
    | ~ ( r1_tarski @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['42','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ sk_D @ ( k10_relat_1 @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['36','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.htE7lTi6zS
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 330 iterations in 0.468s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.74/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.74/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.93  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.74/0.93  thf(sk_D_type, type, sk_D: $i).
% 0.74/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.93  thf(sk_E_type, type, sk_E: $i).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.74/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.93  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.93  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.74/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.93  thf(t172_funct_2, conjecture,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.74/0.93           ( ![C:$i]:
% 0.74/0.93             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.93                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.93               ( ![D:$i]:
% 0.74/0.93                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93                   ( ![E:$i]:
% 0.74/0.93                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.74/0.93                       ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.74/0.93                         ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i]:
% 0.74/0.93        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.74/0.93          ( ![B:$i]:
% 0.74/0.93            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.74/0.93              ( ![C:$i]:
% 0.74/0.93                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/0.93                    ( m1_subset_1 @
% 0.74/0.93                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.93                  ( ![D:$i]:
% 0.74/0.93                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93                      ( ![E:$i]:
% 0.74/0.93                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.74/0.93                          ( ( r1_tarski @ ( k7_relset_1 @ A @ B @ C @ D ) @ E ) <=>
% 0.74/0.93                            ( r1_tarski @ D @ ( k8_relset_1 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t172_funct_2])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.74/0.93        | ~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      ((~ (r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.74/0.93         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k8_relset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.74/0.93          | ((k8_relset_1 @ X30 @ X31 @ X29 @ X32) = (k10_relat_1 @ X29 @ X32)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      ((~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E)))
% 0.74/0.93         <= (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('demod', [status(thm)], ['1', '4'])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.74/0.93       ~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf(t145_funct_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/0.93       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.74/0.93  thf('7', plain,
% 0.74/0.93      (![X17 : $i, X18 : $i]:
% 0.74/0.93         ((r1_tarski @ (k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X18)) @ X18)
% 0.74/0.93          | ~ (v1_funct_1 @ X17)
% 0.74/0.93          | ~ (v1_relat_1 @ X17))),
% 0.74/0.93      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.74/0.93        | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.74/0.93         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf(d10_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.93  thf('10', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.93  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.74/0.93      inference('simplify', [status(thm)], ['10'])).
% 0.74/0.93  thf(t158_relat_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( v1_relat_1 @ C ) =>
% 0.74/0.93       ( ![D:$i]:
% 0.74/0.93         ( ( v1_relat_1 @ D ) =>
% 0.74/0.93           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.74/0.93             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.93         (~ (v1_relat_1 @ X13)
% 0.74/0.93          | (r1_tarski @ (k9_relat_1 @ X14 @ X15) @ (k9_relat_1 @ X13 @ X16))
% 0.74/0.93          | ~ (r1_tarski @ X14 @ X13)
% 0.74/0.93          | ~ (r1_tarski @ X15 @ X16)
% 0.74/0.93          | ~ (v1_relat_1 @ X14))),
% 0.74/0.93      inference('cnf', [status(esa)], [t158_relat_1])).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         (~ (v1_relat_1 @ X0)
% 0.74/0.93          | ~ (r1_tarski @ X2 @ X1)
% 0.74/0.93          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.74/0.93          | ~ (v1_relat_1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['11', '12'])).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.74/0.93          | ~ (r1_tarski @ X2 @ X1)
% 0.74/0.93          | ~ (v1_relat_1 @ X0))),
% 0.74/0.93      inference('simplify', [status(thm)], ['13'])).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      ((![X0 : $i]:
% 0.74/0.93          (~ (v1_relat_1 @ X0)
% 0.74/0.93           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ 
% 0.74/0.93              (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))))
% 0.74/0.93         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['9', '14'])).
% 0.74/0.93  thf(t1_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.74/0.93       ( r1_tarski @ A @ C ) ))).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.74/0.93         (~ (r1_tarski @ X3 @ X4)
% 0.74/0.93          | ~ (r1_tarski @ X4 @ X5)
% 0.74/0.93          | (r1_tarski @ X3 @ X5))),
% 0.74/0.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.74/0.93  thf('17', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i]:
% 0.74/0.93          (~ (v1_relat_1 @ X0)
% 0.74/0.93           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 0.74/0.93           | ~ (r1_tarski @ 
% 0.74/0.93                (k9_relat_1 @ X0 @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)) @ 
% 0.74/0.93                X1)))
% 0.74/0.93         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      ((![X0 : $i, X1 : $i]:
% 0.74/0.93          (~ (v1_relat_1 @ X0)
% 0.74/0.93           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_D) @ X1)
% 0.74/0.93           | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_E)) @ 
% 0.74/0.93                X1)))
% 0.74/0.93         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('demod', [status(thm)], ['17', '18'])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      (((~ (v1_relat_1 @ sk_C)
% 0.74/0.93         | ~ (v1_funct_1 @ sk_C)
% 0.74/0.93         | (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)
% 0.74/0.93         | ~ (v1_relat_1 @ sk_C)))
% 0.74/0.93         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['7', '19'])).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(cc2_relat_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( v1_relat_1 @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      (![X9 : $i, X10 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.74/0.93          | (v1_relat_1 @ X9)
% 0.74/0.93          | ~ (v1_relat_1 @ X10))),
% 0.74/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.74/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.74/0.93  thf(fc6_relat_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.74/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.93  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.74/0.93      inference('demod', [status(thm)], ['23', '24'])).
% 0.74/0.93  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.74/0.93      inference('demod', [status(thm)], ['23', '24'])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.74/0.93         <= (((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.74/0.93      inference('demod', [status(thm)], ['20', '25', '26', '27'])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k7_relset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.74/0.93          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.74/0.93  thf('31', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.93  thf('32', plain,
% 0.74/0.93      ((~ (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.74/0.93         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.74/0.93         <= (~ ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['31', '32'])).
% 0.74/0.93  thf('34', plain,
% 0.74/0.93      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 0.74/0.93       ~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['28', '33'])).
% 0.74/0.93  thf('35', plain,
% 0.74/0.93      (~ ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.74/0.93      inference('sat_resolution*', [status(thm)], ['6', '34'])).
% 0.74/0.93  thf('36', plain, (~ (r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 0.74/0.93      inference('simpl_trail', [status(thm)], ['5', '35'])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))
% 0.74/0.93         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf('38', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E))
% 0.74/0.93         <= (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.74/0.93      inference('demod', [status(thm)], ['37', '38'])).
% 0.74/0.93  thf('40', plain,
% 0.74/0.93      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)) | 
% 0.74/0.93       ((r1_tarski @ sk_D @ (k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (((r1_tarski @ (k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E))),
% 0.74/0.93      inference('sat_resolution*', [status(thm)], ['6', '34', '40'])).
% 0.74/0.93  thf('42', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_D) @ sk_E)),
% 0.74/0.93      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.74/0.93  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(d1_funct_2, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.74/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.74/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.74/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.74/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.74/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_1, axiom,
% 0.74/0.93    (![C:$i,B:$i,A:$i]:
% 0.74/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.74/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.74/0.93         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.74/0.93          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.74/0.93          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.74/0.93  thf('45', plain,
% 0.74/0.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.74/0.93        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['43', '44'])).
% 0.74/0.93  thf(zf_stmt_2, axiom,
% 0.74/0.93    (![B:$i,A:$i]:
% 0.74/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.74/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X33 : $i, X34 : $i]:
% 0.74/0.93         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.74/0.93  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.93  thf('48', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['46', '47'])).
% 0.74/0.93  thf('49', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.74/0.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.74/0.93  thf(zf_stmt_5, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.74/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.74/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.74/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.74/0.93  thf('50', plain,
% 0.74/0.93      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.74/0.93         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.74/0.93          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.74/0.93          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.74/0.93  thf('51', plain,
% 0.74/0.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['49', '50'])).
% 0.74/0.93  thf('52', plain,
% 0.74/0.93      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['48', '51'])).
% 0.74/0.93  thf('53', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('54', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.74/0.93      inference('clc', [status(thm)], ['52', '53'])).
% 0.74/0.93  thf('55', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.74/0.93  thf('56', plain,
% 0.74/0.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.74/0.93         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.74/0.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.74/0.93  thf('57', plain,
% 0.74/0.93      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.74/0.93      inference('sup-', [status(thm)], ['55', '56'])).
% 0.74/0.93  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.74/0.93      inference('demod', [status(thm)], ['45', '54', '57'])).
% 0.74/0.93  thf(t163_funct_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.74/0.93       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.74/0.93           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.74/0.93         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.74/0.93  thf('59', plain,
% 0.74/0.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.74/0.93         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.74/0.93          | ~ (r1_tarski @ (k9_relat_1 @ X20 @ X19) @ X21)
% 0.74/0.93          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ X21))
% 0.74/0.93          | ~ (v1_funct_1 @ X20)
% 0.74/0.93          | ~ (v1_relat_1 @ X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.74/0.93  thf('60', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (~ (r1_tarski @ X0 @ sk_A)
% 0.74/0.93          | ~ (v1_relat_1 @ sk_C)
% 0.74/0.93          | ~ (v1_funct_1 @ sk_C)
% 0.74/0.93          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 0.74/0.93          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 0.74/0.93      inference('sup-', [status(thm)], ['58', '59'])).
% 0.74/0.93  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.74/0.93      inference('demod', [status(thm)], ['23', '24'])).
% 0.74/0.93  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('63', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (~ (r1_tarski @ X0 @ sk_A)
% 0.74/0.93          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_C @ X1))
% 0.74/0.93          | ~ (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ X1))),
% 0.74/0.93      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.74/0.93  thf('64', plain,
% 0.74/0.93      (((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))
% 0.74/0.93        | ~ (r1_tarski @ sk_D @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['42', '63'])).
% 0.74/0.93  thf('65', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t3_subset, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/0.93  thf('66', plain,
% 0.74/0.93      (![X6 : $i, X7 : $i]:
% 0.74/0.93         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('67', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.74/0.93      inference('sup-', [status(thm)], ['65', '66'])).
% 0.74/0.93  thf('68', plain, ((r1_tarski @ sk_D @ (k10_relat_1 @ sk_C @ sk_E))),
% 0.74/0.93      inference('demod', [status(thm)], ['64', '67'])).
% 0.74/0.93  thf('69', plain, ($false), inference('demod', [status(thm)], ['36', '68'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
