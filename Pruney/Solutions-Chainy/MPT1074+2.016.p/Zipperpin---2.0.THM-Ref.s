%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JcZH2zWLuV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:24 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 550 expanded)
%              Number of leaves         :   39 ( 178 expanded)
%              Depth                    :   25
%              Number of atoms          :  970 (9163 expanded)
%              Number of equality atoms :   58 ( 222 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X20 ) ) )
      | ( r2_hidden @ X19 @ ( k1_funct_2 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_funct_2 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_funct_2 @ sk_B @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t169_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_funct_2 @ X22 @ X23 ) )
      | ( ( k1_relat_1 @ X21 )
        = X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t169_funct_2])).

thf('8',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['8','11','12'])).

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

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X2 @ X0 )
      | ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ X15 )
      | ( ( k3_funct_2 @ X15 @ X16 @ X14 @ X17 )
        = ( k1_funct_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['8','11','12'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['8','11','12'])).

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

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != X31 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X32 @ X33 @ X31 ) @ X32 @ X33 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( zip_tseitin_1 @ X32 @ X33 @ ( k1_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X2 @ X0 )
      | ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('38',plain,(
    ! [X34: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X34 ) @ sk_A )
      | ~ ( m1_subset_1 @ X34 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X25 @ X24 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','48'])).

thf('50',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( zip_tseitin_1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
      = ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['61','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JcZH2zWLuV
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 139 iterations in 0.184s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.47/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.64  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.64  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(t191_funct_2, conjecture,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.64       ( ![C:$i]:
% 0.47/0.64         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.47/0.64           ( ![D:$i]:
% 0.47/0.64             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.47/0.64                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.47/0.64               ( ( ![E:$i]:
% 0.47/0.64                   ( ( m1_subset_1 @ E @ B ) =>
% 0.47/0.64                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.47/0.64                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i]:
% 0.47/0.64        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.64          ( ![C:$i]:
% 0.47/0.64            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.47/0.64              ( ![D:$i]:
% 0.47/0.64                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.47/0.64                    ( m1_subset_1 @
% 0.47/0.64                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.47/0.64                  ( ( ![E:$i]:
% 0.47/0.64                      ( ( m1_subset_1 @ E @ B ) =>
% 0.47/0.64                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.47/0.64                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.47/0.64  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t11_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.64         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.64         (((X20) = (k1_xboole_0))
% 0.47/0.64          | ~ (v1_funct_1 @ X19)
% 0.47/0.64          | ~ (v1_funct_2 @ X19 @ X18 @ X20)
% 0.47/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X20)))
% 0.47/0.64          | (r2_hidden @ X19 @ (k1_funct_2 @ X18 @ X20)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (((r2_hidden @ sk_D_1 @ (k1_funct_2 @ sk_B @ sk_C))
% 0.47/0.64        | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (((r2_hidden @ sk_D_1 @ (k1_funct_2 @ sk_B @ sk_C))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.47/0.64  thf(t169_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.64       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.47/0.64         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.47/0.64           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X21 @ (k1_funct_2 @ X22 @ X23))
% 0.47/0.64          | ((k1_relat_1 @ X21) = (X22))
% 0.47/0.64          | ~ (v1_funct_1 @ X21)
% 0.47/0.64          | ~ (v1_relat_1 @ X21))),
% 0.47/0.64      inference('cnf', [status(esa)], [t169_funct_2])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_D_1)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.64        | ((k1_relat_1 @ sk_D_1) = (sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(cc1_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( v1_relat_1 @ C ) ))).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         ((v1_relat_1 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.64  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('12', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_1) = (sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['8', '11', '12'])).
% 0.47/0.64  thf(t5_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.47/0.64       ( ( ( ![D:$i]:
% 0.47/0.64             ( ( r2_hidden @ D @ A ) =>
% 0.47/0.64               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.47/0.64           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.47/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.64           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_1, axiom,
% 0.47/0.64    (![D:$i,C:$i,B:$i,A:$i]:
% 0.47/0.64     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.47/0.64       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27) | (r2_hidden @ X24 @ X27))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.64  thf(t1_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [t1_subset])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X1 @ X3 @ X2 @ X0) | (m1_subset_1 @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(redefinition_k3_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.47/0.64         ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.64         ( m1_subset_1 @ D @ A ) ) =>
% 0.47/0.64       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.47/0.64          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.47/0.64          | ~ (v1_funct_1 @ X14)
% 0.47/0.64          | (v1_xboole_0 @ X15)
% 0.47/0.64          | ~ (m1_subset_1 @ X17 @ X15)
% 0.47/0.64          | ((k3_funct_2 @ X15 @ X16 @ X14 @ X17) = (k1_funct_1 @ X14 @ X17)))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.47/0.64            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.47/0.64          | (v1_xboole_0 @ sk_B)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.64          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.64  thf('20', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('21', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.47/0.64            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.47/0.64          | (v1_xboole_0 @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.47/0.64  thf('23', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.47/0.64          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.47/0.64              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.47/0.64      inference('clc', [status(thm)], ['22', '23'])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X0 @ X2 @ X1 @ sk_B)
% 0.47/0.64          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.47/0.64              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['16', '24'])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_1) = (sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['8', '11', '12'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_D_1) = (sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['8', '11', '12'])).
% 0.47/0.64  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.64  thf(zf_stmt_3, axiom,
% 0.47/0.64    (![C:$i,B:$i,A:$i]:
% 0.47/0.64     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.64       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.47/0.64  thf(zf_stmt_5, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.64       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.47/0.64           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.47/0.64         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.64         (((k1_relat_1 @ X32) != (X31))
% 0.47/0.64          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ X31) @ X32 @ X33 @ X31)
% 0.47/0.64          | (zip_tseitin_1 @ X32 @ X33 @ X31)
% 0.47/0.64          | ~ (v1_funct_1 @ X32)
% 0.47/0.64          | ~ (v1_relat_1 @ X32))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X32 : $i, X33 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X32)
% 0.47/0.64          | ~ (v1_funct_1 @ X32)
% 0.47/0.64          | (zip_tseitin_1 @ X32 @ X33 @ (k1_relat_1 @ X32))
% 0.47/0.64          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ (k1_relat_1 @ X32)) @ X32 @ 
% 0.47/0.64               X33 @ (k1_relat_1 @ X32)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.47/0.64             (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ~ (v1_funct_1 @ sk_D_1)
% 0.47/0.64          | ~ (v1_relat_1 @ sk_D_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['27', '29'])).
% 0.47/0.64  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.47/0.64             (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.47/0.64      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['26', '33'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | ~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B))),
% 0.47/0.64      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.47/0.64            = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['25', '35'])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X1 @ X3 @ X2 @ X0) | (m1_subset_1 @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X34 : $i]:
% 0.47/0.64         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X34) @ sk_A)
% 0.47/0.64          | ~ (m1_subset_1 @ X34 @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X0 @ X2 @ X1 @ sk_B)
% 0.47/0.64          | (r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0) @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | ~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B))),
% 0.47/0.64      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ 
% 0.47/0.64           (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.47/0.64           sk_A)
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.47/0.64           sk_A)
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['36', '41'])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.47/0.64             sk_A))),
% 0.47/0.64      inference('simplify', [status(thm)], ['42'])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.64         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.47/0.64          | ~ (r2_hidden @ (k1_funct_1 @ X25 @ X24) @ X26))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.47/0.64             (k1_relat_1 @ sk_D_1))
% 0.47/0.64          | ((sk_C) = (k1_xboole_0))
% 0.47/0.64          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.47/0.64      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | (zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64        | (zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B)
% 0.47/0.64        | ((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['13', '48'])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_A @ sk_B))),
% 0.47/0.64      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.47/0.64          | ~ (zip_tseitin_1 @ X28 @ X29 @ X30))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.47/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.64  thf(dt_k2_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (k2_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.47/0.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | (m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 0.47/0.64           (k1_zfmisc_1 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.64  thf(t3_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (![X2 : $i, X3 : $i]:
% 0.47/0.64         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0))
% 0.47/0.64        | (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)
% 0.47/0.64        | ((sk_C) = (k1_xboole_0))
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['54', '59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 0.47/0.64      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.64         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.47/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.64  thf('66', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.47/0.64      inference('demod', [status(thm)], ['62', '65'])).
% 0.47/0.64  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.47/0.64      inference('clc', [status(thm)], ['61', '66'])).
% 0.47/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.64  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('69', plain, ($false),
% 0.47/0.64      inference('demod', [status(thm)], ['0', '67', '68'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
