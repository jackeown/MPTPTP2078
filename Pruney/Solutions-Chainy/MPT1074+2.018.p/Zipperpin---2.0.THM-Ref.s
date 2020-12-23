%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i4NmfjX8OZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 191 expanded)
%              Number of leaves         :   39 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  766 (2316 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['13','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ X21 )
      | ( ( k3_funct_2 @ X21 @ X22 @ X20 @ X23 )
        = ( k1_funct_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('38',plain,(
    ! [X34: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X34 ) @ sk_A )
      | ~ ( m1_subset_1 @ X34 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ sk_A )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X25 @ X24 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( zip_tseitin_1 @ X32 @ X33 @ ( k1_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('45',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( zip_tseitin_1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v5_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('57',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i4NmfjX8OZ
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:27:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 56 iterations in 0.025s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(t191_funct_2, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.50           ( ![D:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.50                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.50               ( ( ![E:$i]:
% 0.22/0.50                   ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.50                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.22/0.50                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.50          ( ![C:$i]:
% 0.22/0.50            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.50              ( ![D:$i]:
% 0.22/0.50                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.50                    ( m1_subset_1 @
% 0.22/0.50                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.50                  ( ( ![E:$i]:
% 0.22/0.50                      ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.50                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.22/0.50                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.22/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf(t5_funct_2, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.22/0.50       ( ( ( ![D:$i]:
% 0.22/0.50             ( ( r2_hidden @ D @ A ) =>
% 0.22/0.50               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.22/0.50           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.50           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, axiom,
% 0.22/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.22/0.50       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27) | (r2_hidden @ X24 @ X27))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_3, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.50       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_5, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.22/0.50           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.22/0.50         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.50         (((k1_relat_1 @ X32) != (X31))
% 0.22/0.50          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ X31) @ X32 @ X33 @ X31)
% 0.22/0.50          | (zip_tseitin_1 @ X32 @ X33 @ X31)
% 0.22/0.50          | ~ (v1_funct_1 @ X32)
% 0.22/0.50          | ~ (v1_relat_1 @ X32))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X32)
% 0.22/0.50          | ~ (v1_funct_1 @ X32)
% 0.22/0.50          | (zip_tseitin_1 @ X32 @ X33 @ (k1_relat_1 @ X32))
% 0.22/0.50          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ (k1_relat_1 @ X32)) @ X32 @ 
% 0.22/0.50               X33 @ (k1_relat_1 @ X32)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.22/0.50          | (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X14 @ X15)
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('11', plain, ((v4_relat_1 @ sk_D_1 @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(d18_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (v4_relat_1 @ X8 @ X9)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.22/0.50          | ~ (v1_relat_1 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.50          | (v1_relat_1 @ X6)
% 0.22/0.50          | ~ (v1_relat_1 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf(fc6_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf(t4_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.50          | (m1_subset_1 @ X3 @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ sk_D_1)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.50          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '23'])).
% 0.22/0.50  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('26', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k3_funct_2, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.50         ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.50         ( m1_subset_1 @ D @ A ) ) =>
% 0.22/0.50       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.22/0.50          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.22/0.50          | ~ (v1_funct_1 @ X20)
% 0.22/0.50          | (v1_xboole_0 @ X21)
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ X21)
% 0.22/0.50          | ((k3_funct_2 @ X21 @ X22 @ X20 @ X23) = (k1_funct_1 @ X20 @ X23)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.22/0.50            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | (v1_xboole_0 @ sk_B)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.50          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.22/0.50            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.22/0.50  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.22/0.50              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.22/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ 
% 0.22/0.50              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.22/0.50              = (k1_funct_1 @ sk_D_1 @ 
% 0.22/0.50                 (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X34 : $i]:
% 0.22/0.50         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X34) @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X34 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ 
% 0.22/0.50              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.22/0.50             sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ 
% 0.22/0.50           (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.22/0.50           sk_A)
% 0.22/0.50          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['36', '39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k1_funct_1 @ sk_D_1 @ 
% 0.22/0.50              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.22/0.50             sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.22/0.50          | ~ (r2_hidden @ (k1_funct_1 @ X25 @ X24) @ X26))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50          | (zip_tseitin_0 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 0.22/0.50             sk_D_1 @ sk_A @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X32)
% 0.22/0.50          | ~ (v1_funct_1 @ X32)
% 0.22/0.50          | (zip_tseitin_1 @ X32 @ X33 @ (k1_relat_1 @ X32))
% 0.22/0.50          | ~ (zip_tseitin_0 @ (sk_D @ X32 @ X33 @ (k1_relat_1 @ X32)) @ X32 @ 
% 0.22/0.50               X33 @ (k1_relat_1 @ X32)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50        | (zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.50        | ~ (v1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.22/0.50        | (zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.22/0.50  thf('49', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.22/0.50          | ~ (zip_tseitin_1 @ X28 @ X29 @ X30))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.22/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((v5_relat_1 @ X14 @ X16)
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('53', plain, ((v5_relat_1 @ sk_D_1 @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.50  thf(d19_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (v5_relat_1 @ X10 @ X11)
% 0.22/0.50          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.22/0.50          | ~ (v1_relat_1 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.50  thf('56', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('57', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.22/0.50  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
