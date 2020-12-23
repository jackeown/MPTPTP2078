%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V72yK6KiV2

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 647 expanded)
%              Number of leaves         :   49 ( 217 expanded)
%              Depth                    :   25
%              Number of atoms          :  921 (8827 expanded)
%              Number of equality atoms :   33 ( 166 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_2 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['19','22'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['11','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','29','32'])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relat_1 @ X40 )
       != X39 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X40 @ X41 @ X39 ) @ X40 @ X41 @ X39 )
      | ( zip_tseitin_3 @ X40 @ X41 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('35',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ( zip_tseitin_3 @ X40 @ X41 @ ( k1_relat_1 @ X40 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X40 @ X41 @ ( k1_relat_1 @ X40 ) ) @ X40 @ X41 @ ( k1_relat_1 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','29','32'])).

thf('38',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','29','32'])).

thf('39',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','41'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ( ( k3_funct_2 @ X29 @ X30 @ X28 @ X31 )
        = ( k1_funct_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('55',plain,(
    ! [X42: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X42 ) @ sk_A )
      | ~ ( m1_subset_1 @ X42 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_2 @ X32 @ X33 @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X33 @ X32 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('62',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( zip_tseitin_3 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('65',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v5_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['4','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V72yK6KiV2
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 119 iterations in 0.126s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.59  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.20/0.59  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.20/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.59  thf(t191_funct_2, conjecture,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.59       ( ![C:$i]:
% 0.20/0.59         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.59           ( ![D:$i]:
% 0.20/0.59             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.59                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.59               ( ( ![E:$i]:
% 0.20/0.59                   ( ( m1_subset_1 @ E @ B ) =>
% 0.20/0.59                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.20/0.59                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i]:
% 0.20/0.59        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.59          ( ![C:$i]:
% 0.20/0.59            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.59              ( ![D:$i]:
% 0.20/0.59                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.59                    ( m1_subset_1 @
% 0.20/0.59                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.59                  ( ( ![E:$i]:
% 0.20/0.59                      ( ( m1_subset_1 @ E @ B ) =>
% 0.20/0.59                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.20/0.59                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.59         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.20/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.59  thf(t5_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.20/0.59       ( ( ( ![D:$i]:
% 0.20/0.59             ( ( r2_hidden @ D @ A ) =>
% 0.20/0.59               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.20/0.59           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.59           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_1, axiom,
% 0.20/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.59     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.20/0.59       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.59         ((zip_tseitin_2 @ X32 @ X33 @ X34 @ X35) | (r2_hidden @ X32 @ X35))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.59  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d1_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_2, axiom,
% 0.20/0.59    (![C:$i,B:$i,A:$i]:
% 0.20/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.59         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.20/0.59          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.20/0.59          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.20/0.59        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.59  thf(zf_stmt_5, axiom,
% 0.20/0.59    (![B:$i,A:$i]:
% 0.20/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.59  thf(zf_stmt_6, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.59         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.20/0.59          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.20/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.20/0.59        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X20 : $i, X21 : $i]:
% 0.20/0.59         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.59  thf('13', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.20/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(cc2_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.59         ((v5_relat_1 @ X11 @ X13)
% 0.20/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.59  thf('17', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.59  thf(d19_relat_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( v1_relat_1 @ B ) =>
% 0.20/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X6 : $i, X7 : $i]:
% 0.20/0.59         (~ (v5_relat_1 @ X6 @ X7)
% 0.20/0.59          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.20/0.59          | ~ (v1_relat_1 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(cc1_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( v1_relat_1 @ C ) ))).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.59         ((v1_relat_1 @ X8)
% 0.20/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.59  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.59  thf(t1_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.59       ( r1_tarski @ A @ C ) ))).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.59          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.59          | (r1_tarski @ X0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((zip_tseitin_0 @ sk_C @ X1)
% 0.20/0.59          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['14', '25'])).
% 0.20/0.59  thf('27', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.59  thf('28', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('29', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.20/0.59      inference('demod', [status(thm)], ['11', '28'])).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.59  thf('31', plain,
% 0.20/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.59         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.20/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.59  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['8', '29', '32'])).
% 0.20/0.59  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.20/0.59  thf(zf_stmt_8, axiom,
% 0.20/0.59    (![C:$i,B:$i,A:$i]:
% 0.20/0.59     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.20/0.59       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.20/0.59  thf(zf_stmt_10, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.59       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.59           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.20/0.59         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X40) != (X39))
% 0.20/0.59          | ~ (zip_tseitin_2 @ (sk_D @ X40 @ X41 @ X39) @ X40 @ X41 @ X39)
% 0.20/0.59          | (zip_tseitin_3 @ X40 @ X41 @ X39)
% 0.20/0.59          | ~ (v1_funct_1 @ X40)
% 0.20/0.59          | ~ (v1_relat_1 @ X40))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (![X40 : $i, X41 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X40)
% 0.20/0.59          | ~ (v1_funct_1 @ X40)
% 0.20/0.59          | (zip_tseitin_3 @ X40 @ X41 @ (k1_relat_1 @ X40))
% 0.20/0.59          | ~ (zip_tseitin_2 @ (sk_D @ X40 @ X41 @ (k1_relat_1 @ X40)) @ X40 @ 
% 0.20/0.59               X41 @ (k1_relat_1 @ X40)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.20/0.59             (k1_relat_1 @ sk_D_1))
% 0.20/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.20/0.59          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.59          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.59  thf('37', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['8', '29', '32'])).
% 0.20/0.59  thf('38', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['8', '29', '32'])).
% 0.20/0.59  thf('39', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 0.20/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['5', '41'])).
% 0.20/0.59  thf(t1_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.59  thf('43', plain,
% 0.20/0.59      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.59         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.59         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.59       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.20/0.59          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.20/0.59          | ~ (v1_funct_1 @ X28)
% 0.20/0.59          | (v1_xboole_0 @ X29)
% 0.20/0.59          | ~ (m1_subset_1 @ X31 @ X29)
% 0.20/0.59          | ((k3_funct_2 @ X29 @ X30 @ X28 @ X31) = (k1_funct_1 @ X28 @ X31)))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.20/0.59            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.59          | (v1_xboole_0 @ sk_B)
% 0.20/0.59          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.59          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.20/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.59  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('49', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.20/0.59            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.59          | (v1_xboole_0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.59  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.59          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.20/0.59              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.20/0.59      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.20/0.59              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['44', '52'])).
% 0.20/0.59  thf('54', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.59  thf('55', plain,
% 0.20/0.59      (![X42 : $i]:
% 0.20/0.59         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X42) @ sk_A)
% 0.20/0.59          | ~ (m1_subset_1 @ X42 @ sk_B))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('56', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (r2_hidden @ 
% 0.20/0.59             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.20/0.59             sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.20/0.59           sk_A)
% 0.20/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['53', '56'])).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.20/0.59             sk_A))),
% 0.20/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.59         ((zip_tseitin_2 @ X32 @ X33 @ X34 @ X35)
% 0.20/0.59          | ~ (r2_hidden @ (k1_funct_1 @ X33 @ X32) @ X34))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.59  thf('61', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 0.20/0.59        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.59  thf('63', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.59      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.59  thf('64', plain,
% 0.20/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.59         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.20/0.59          | ~ (zip_tseitin_3 @ X36 @ X37 @ X38))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.59  thf('65', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.59         ((v5_relat_1 @ X11 @ X13)
% 0.20/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.59  thf('67', plain, ((v5_relat_1 @ sk_D_1 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.59  thf('68', plain,
% 0.20/0.59      (![X6 : $i, X7 : $i]:
% 0.20/0.59         (~ (v5_relat_1 @ X6 @ X7)
% 0.20/0.59          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.20/0.59          | ~ (v1_relat_1 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.59  thf('70', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('71', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.59  thf('72', plain, ($false), inference('demod', [status(thm)], ['4', '71'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
