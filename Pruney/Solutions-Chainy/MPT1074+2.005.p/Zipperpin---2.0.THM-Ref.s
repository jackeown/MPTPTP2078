%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h2d4Br1VCQ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 293 expanded)
%              Number of leaves         :   38 ( 104 expanded)
%              Depth                    :   21
%              Number of atoms          :  790 (4071 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_0 @ D @ C @ B @ A ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != X31 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X32 @ X33 @ X31 ) @ X32 @ X33 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( zip_tseitin_1 @ X32 @ X33 @ ( k1_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('11',plain,(
    v4_relat_1 @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ X21 )
      | ( ( k3_funct_2 @ X21 @ X22 @ X20 @ X23 )
        = ( k1_funct_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('36',plain,(
    ! [X34: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X34 ) @ sk_A )
      | ~ ( m1_subset_1 @ X34 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ sk_A )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X25 @ X24 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( zip_tseitin_1 @ X32 @ X33 @ ( k1_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( zip_tseitin_1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('51',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    r1_tarski @ ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h2d4Br1VCQ
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 64 iterations in 0.028s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.45  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.45  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.45  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(t191_funct_2, conjecture,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.45       ( ![C:$i]:
% 0.21/0.45         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.45           ( ![D:$i]:
% 0.21/0.45             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.45                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.45               ( ( ![E:$i]:
% 0.21/0.45                   ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.45                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.21/0.45                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]:
% 0.21/0.45        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.45          ( ![C:$i]:
% 0.21/0.45            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.45              ( ![D:$i]:
% 0.21/0.45                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.45                    ( m1_subset_1 @
% 0.21/0.45                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.45                  ( ( ![E:$i]:
% 0.21/0.45                      ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.45                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.21/0.45                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.45         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.21/0.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.21/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.45  thf(t5_funct_2, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.45       ( ( ( ![D:$i]:
% 0.21/0.45             ( ( r2_hidden @ D @ A ) =>
% 0.21/0.45               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.21/0.45           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.45           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_1, axiom,
% 0.21/0.45    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.45     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.21/0.45       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.45         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27) | (r2_hidden @ X24 @ X27))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.45  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.45  thf(zf_stmt_3, axiom,
% 0.21/0.45    (![C:$i,B:$i,A:$i]:
% 0.21/0.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.45       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.45  thf(zf_stmt_5, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.45       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.45           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.21/0.45         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.45         (((k1_relat_1 @ X32) != (X31))
% 0.21/0.45          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ X31) @ X32 @ X33 @ X31)
% 0.21/0.45          | (zip_tseitin_1 @ X32 @ X33 @ X31)
% 0.21/0.45          | ~ (v1_funct_1 @ X32)
% 0.21/0.45          | ~ (v1_relat_1 @ X32))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X32 : $i, X33 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X32)
% 0.21/0.45          | ~ (v1_funct_1 @ X32)
% 0.21/0.45          | (zip_tseitin_1 @ X32 @ X33 @ (k1_relat_1 @ X32))
% 0.21/0.45          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ (k1_relat_1 @ X32)) @ X32 @ 
% 0.21/0.45               X33 @ (k1_relat_1 @ X32)))),
% 0.21/0.45      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((r2_hidden @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.21/0.45          | (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.45          | ~ (v1_funct_1 @ X0)
% 0.21/0.45          | ~ (v1_relat_1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(cc2_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.45         ((v4_relat_1 @ X11 @ X12)
% 0.21/0.45          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.45  thf('11', plain, ((v4_relat_1 @ sk_D_1 @ sk_B)),
% 0.21/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf(d18_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ B ) =>
% 0.21/0.45       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X6 : $i, X7 : $i]:
% 0.21/0.45         (~ (v4_relat_1 @ X6 @ X7)
% 0.21/0.45          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.21/0.45          | ~ (v1_relat_1 @ X6))),
% 0.21/0.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(cc1_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( v1_relat_1 @ C ) ))).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.45         ((v1_relat_1 @ X8)
% 0.21/0.45          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.45  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_B)),
% 0.21/0.45      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.45  thf(t3_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.45  thf('18', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.45  thf(t4_subset, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.45       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.45  thf('20', plain,
% 0.21/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.45          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.45          | (m1_subset_1 @ X3 @ X5))),
% 0.21/0.45      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((m1_subset_1 @ X0 @ sk_B)
% 0.21/0.45          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.45  thf('22', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ sk_D_1)
% 0.21/0.45          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.45          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B))),
% 0.21/0.45      inference('sup-', [status(thm)], ['8', '21'])).
% 0.21/0.45  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('24', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('25', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.45  thf('26', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.45     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.45         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.45         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.45       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.45  thf('27', plain,
% 0.21/0.45      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.45          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.21/0.45          | ~ (v1_funct_1 @ X20)
% 0.21/0.45          | (v1_xboole_0 @ X21)
% 0.21/0.45          | ~ (m1_subset_1 @ X23 @ X21)
% 0.21/0.45          | ((k3_funct_2 @ X21 @ X22 @ X20 @ X23) = (k1_funct_1 @ X20 @ X23)))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.45  thf('28', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.45            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.21/0.45          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.45          | (v1_xboole_0 @ sk_B)
% 0.21/0.45          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.45          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.21/0.45      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.45  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('30', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('31', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.45            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.21/0.45          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.45          | (v1_xboole_0 @ sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.45  thf('32', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('33', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.45          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.45              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.21/0.45      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.45  thf('34', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ 
% 0.21/0.45              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.21/0.45              = (k1_funct_1 @ sk_D_1 @ 
% 0.21/0.45                 (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))))),
% 0.21/0.45      inference('sup-', [status(thm)], ['25', '33'])).
% 0.21/0.45  thf('35', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B))),
% 0.21/0.45      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.45  thf('36', plain,
% 0.21/0.45      (![X34 : $i]:
% 0.21/0.45         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X34) @ sk_A)
% 0.21/0.45          | ~ (m1_subset_1 @ X34 @ sk_B))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('37', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (r2_hidden @ 
% 0.21/0.45             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ 
% 0.21/0.45              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.21/0.45             sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.45  thf('38', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((r2_hidden @ 
% 0.21/0.45           (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.21/0.45           sk_A)
% 0.21/0.45          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.45      inference('sup+', [status(thm)], ['34', '37'])).
% 0.21/0.45  thf('39', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (r2_hidden @ 
% 0.21/0.45             (k1_funct_1 @ sk_D_1 @ 
% 0.21/0.45              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.21/0.45             sk_A))),
% 0.21/0.45      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.45  thf('40', plain,
% 0.21/0.45      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.45         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.45          | ~ (r2_hidden @ (k1_funct_1 @ X25 @ X24) @ X26))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.45  thf('41', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 0.21/0.45             sk_D_1 @ sk_A @ X1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.45  thf('42', plain,
% 0.21/0.45      (![X32 : $i, X33 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ X32)
% 0.21/0.45          | ~ (v1_funct_1 @ X32)
% 0.21/0.45          | (zip_tseitin_1 @ X32 @ X33 @ (k1_relat_1 @ X32))
% 0.21/0.45          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ (k1_relat_1 @ X32)) @ X32 @ 
% 0.21/0.45               X33 @ (k1_relat_1 @ X32)))),
% 0.21/0.45      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.45  thf('43', plain,
% 0.21/0.45      (((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45        | (zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.45        | ~ (v1_relat_1 @ sk_D_1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.45  thf('44', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.45  thf('46', plain,
% 0.21/0.45      (((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.21/0.45        | (zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.45      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.45  thf('47', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.21/0.45      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.45  thf('48', plain,
% 0.21/0.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.45         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.21/0.45          | ~ (zip_tseitin_1 @ X28 @ X29 @ X30))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.45  thf('49', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.45  thf(dt_k2_relset_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.45       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.45  thf('50', plain,
% 0.21/0.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.45         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.21/0.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.45      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.45  thf('51', plain,
% 0.21/0.45      ((m1_subset_1 @ (k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_A @ sk_D_1) @ 
% 0.21/0.45        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.45      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.45  thf('52', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.45  thf('53', plain,
% 0.21/0.45      ((r1_tarski @ (k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_A @ sk_D_1) @ 
% 0.21/0.45        sk_A)),
% 0.21/0.45      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.45  thf('54', plain,
% 0.21/0.45      ((m1_subset_1 @ sk_D_1 @ 
% 0.21/0.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.45  thf('55', plain,
% 0.21/0.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.45         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.21/0.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.45  thf('56', plain,
% 0.21/0.45      (((k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_A @ sk_D_1)
% 0.21/0.45         = (k2_relat_1 @ sk_D_1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.45  thf('57', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.21/0.45      inference('demod', [status(thm)], ['53', '56'])).
% 0.21/0.45  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
