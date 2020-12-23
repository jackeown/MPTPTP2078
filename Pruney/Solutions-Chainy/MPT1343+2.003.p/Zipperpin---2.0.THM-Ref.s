%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WiNipl6DLs

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:27 EST 2020

% Result     : Theorem 6.45s
% Output     : Refutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  313 (1278 expanded)
%              Number of leaves         :   64 ( 420 expanded)
%              Depth                    :   27
%              Number of atoms          : 2276 (23181 expanded)
%              Number of equality atoms :  180 (1011 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t67_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                          = ( k2_struct_0 @ B ) )
                        & ( v2_funct_1 @ C ) )
                     => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                        = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tops_2])).

thf('3',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_D )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) )
      | ( ( k7_relset_1 @ X72 @ X73 @ X71 @ X74 )
        = ( k9_relat_1 @ X71 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_C_1 @ sk_D )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) @ sk_D ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_D )
     != ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('14',plain,(
    ! [X85: $i,X86: $i,X87: $i] :
      ( ( ( k2_relset_1 @ X86 @ X85 @ X87 )
       != X85 )
      | ~ ( v2_funct_1 @ X87 )
      | ( ( k2_tops_2 @ X86 @ X85 @ X87 )
        = ( k2_funct_1 @ X87 ) )
      | ~ ( m1_subset_1 @ X87 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X85 ) ) )
      | ~ ( v1_funct_2 @ X87 @ X86 @ X85 )
      | ~ ( v1_funct_1 @ X87 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_relat_1 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X48: $i,X49: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X57: $i] :
      ( ~ ( v2_funct_1 @ X57 )
      | ( ( k2_funct_1 @ X57 )
        = ( k4_relat_1 @ X57 ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','21','31','32','37'])).

thf('39',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k9_relat_1 @ sk_C_1 @ sk_D )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ sk_D ) ),
    inference(demod,[status(thm)],['8','39','40'])).

thf('42',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_D )
     != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ( k9_relat_1 @ sk_C_1 @ sk_D )
 != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_D )
     != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k9_relat_1 @ sk_C_1 @ sk_D )
 != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X63: $i] :
      ( ~ ( v2_funct_1 @ X63 )
      | ( ( k2_relat_1 @ X63 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X63 ) ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('55',plain,(
    ! [X56: $i] :
      ( ( r1_tarski @ X56 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('56',plain,
    ( ( r1_tarski @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('58',plain,(
    ! [X63: $i] :
      ( ~ ( v2_funct_1 @ X63 )
      | ( ( k1_relat_1 @ X63 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X63 ) ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('59',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X58: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X58 ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    r1_tarski @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['56','63','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('72',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( ( k2_relset_1 @ X69 @ X70 @ X68 )
        = ( k2_relat_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('73',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['70','75'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('77',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('79',plain,(
    ! [X75: $i,X76: $i,X77: $i,X78: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X76 @ X77 ) ) )
      | ( ( k8_relset_1 @ X76 @ X77 @ X75 @ X78 )
        = ( k10_relat_1 @ X75 @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('82',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v2_funct_1 @ X61 )
      | ( ( k9_relat_1 @ X61 @ X62 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X61 ) @ X62 ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( v4_relat_1 @ X65 @ X66 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('92',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54
        = ( k7_relat_1 @ X54 @ X55 ) )
      | ~ ( v4_relat_1 @ X54 @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( ( k4_relat_1 @ sk_C_1 )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('95',plain,
    ( ( k4_relat_1 @ sk_C_1 )
    = ( k7_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('97',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('99',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X84: $i] :
      ( ( ( k2_struct_0 @ X84 )
        = ( u1_struct_0 @ X84 ) )
      | ~ ( l1_struct_0 @ X84 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('103',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( v4_relat_1 @ X65 @ X66 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('105',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54
        = ( k7_relat_1 @ X54 @ X55 ) )
      | ~ ( v4_relat_1 @ X54 @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('109',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('112',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('113',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('114',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','114'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('116',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('117',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('118',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X60 @ ( k2_relat_1 @ X59 ) )
      | ( ( k10_relat_1 @ X59 @ ( k1_tarski @ X60 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('121',plain,(
    ! [X53: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X53 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('125',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('128',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('129',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['115','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('133',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ( X81 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X82 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X81 ) ) )
      | ( v1_partfun1 @ X82 @ X83 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X81 ) ) )
      | ~ ( v1_funct_2 @ X82 @ X83 @ X81 )
      | ~ ( v1_funct_1 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('134',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( v1_funct_2 @ X82 @ X83 @ X81 )
      | ( v1_partfun1 @ X82 @ X83 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X81 ) ) )
      | ~ ( v1_funct_1 @ X82 )
      | ( X81 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('139',plain,(
    ! [X79: $i,X80: $i] :
      ( ~ ( v1_partfun1 @ X80 @ X79 )
      | ( ( k1_relat_1 @ X80 )
        = X79 )
      | ~ ( v4_relat_1 @ X80 @ X79 )
      | ~ ( v1_relat_1 @ X80 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('140',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('142',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( v4_relat_1 @ X65 @ X66 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('144',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('148',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X36 @ X37 )
        = k1_xboole_0 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('149',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','149'])).

thf('151',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('152',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( v4_relat_1 @ X65 @ X66 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v4_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54
        = ( k7_relat_1 @ X54 @ X55 ) )
      | ~ ( v4_relat_1 @ X54 @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1
        = ( k7_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1
        = ( k7_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = ( k9_relat_1 @ sk_C_1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('162',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = ( k9_relat_1 @ sk_C_1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('166',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('168',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X36 @ X37 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('169',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['167','169'])).

thf('171',plain,(
    ! [X56: $i] :
      ( ( r1_tarski @ X56 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('173',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('174',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('175',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['172','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['171','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','179'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['126','129'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['166','182'])).

thf('184',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('185',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['163','185'])).

thf('187',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','186'])).

thf('188',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141','144'])).

thf('189',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('191',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['188','191'])).

thf('193',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('194',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('196',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['187','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['197','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( k1_xboole_0
        = ( k7_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','201'])).

thf('203',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('207',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['126','129'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['205','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','211'])).

thf('213',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['126','129'])).

thf('214',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['100','215'])).

thf('217',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('219',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['171','178'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['126','129'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['217','224'])).

thf('226',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('227',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['216','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('230',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('231',plain,(
    ! [X75: $i,X76: $i,X77: $i,X78: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X76 @ X77 ) ) )
      | ( ( k8_relset_1 @ X76 @ X77 @ X75 @ X78 )
        = ( k10_relat_1 @ X75 @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X53: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X53 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('234',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k8_relset_1 @ X3 @ X2 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['229','234'])).

thf('236',plain,(
    ( k9_relat_1 @ sk_C_1 @ sk_D )
 != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('237',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_D )
     != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('240',plain,(
    ! [X53: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X53 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['238','241'])).

thf('243',plain,(
    ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['237','242'])).

thf('244',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['228','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C_1 ) @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','244'])).

thf('246',plain,(
    ( k9_relat_1 @ sk_C_1 @ sk_D )
 != ( k9_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['47','245'])).

thf('247',plain,(
    $false ),
    inference(simplify,[status(thm)],['246'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WiNipl6DLs
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.45/6.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.45/6.75  % Solved by: fo/fo7.sh
% 6.45/6.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.45/6.75  % done 9909 iterations in 6.286s
% 6.45/6.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.45/6.75  % SZS output start Refutation
% 6.45/6.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.45/6.75  thf(sk_B_type, type, sk_B: $i).
% 6.45/6.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 6.45/6.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.45/6.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.45/6.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.45/6.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.45/6.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.45/6.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.45/6.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.45/6.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.45/6.75  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 6.45/6.75  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 6.45/6.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.45/6.75  thf(sk_D_type, type, sk_D: $i).
% 6.45/6.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.45/6.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.45/6.75  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 6.45/6.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.45/6.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.45/6.75  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 6.45/6.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.45/6.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.45/6.75  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 6.45/6.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.45/6.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.45/6.75  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 6.45/6.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.45/6.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.45/6.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.45/6.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.45/6.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.45/6.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.45/6.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.45/6.75  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.45/6.75  thf(sk_A_type, type, sk_A: $i).
% 6.45/6.75  thf(d3_struct_0, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 6.45/6.75  thf('0', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf('1', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf('2', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf(t67_tops_2, conjecture,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( l1_struct_0 @ A ) =>
% 6.45/6.75       ( ![B:$i]:
% 6.45/6.75         ( ( l1_struct_0 @ B ) =>
% 6.45/6.75           ( ![C:$i]:
% 6.45/6.75             ( ( ( v1_funct_1 @ C ) & 
% 6.45/6.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.45/6.75                 ( m1_subset_1 @
% 6.45/6.75                   C @ 
% 6.45/6.75                   ( k1_zfmisc_1 @
% 6.45/6.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.45/6.75               ( ![D:$i]:
% 6.45/6.75                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.45/6.75                   ( ( ( ( k2_relset_1 @
% 6.45/6.75                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 6.45/6.75                         ( k2_struct_0 @ B ) ) & 
% 6.45/6.75                       ( v2_funct_1 @ C ) ) =>
% 6.45/6.75                     ( ( k7_relset_1 @
% 6.45/6.75                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 6.45/6.75                       ( k8_relset_1 @
% 6.45/6.75                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.45/6.75                         ( k2_tops_2 @
% 6.45/6.75                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 6.45/6.75                         D ) ) ) ) ) ) ) ) ) ))).
% 6.45/6.75  thf(zf_stmt_0, negated_conjecture,
% 6.45/6.75    (~( ![A:$i]:
% 6.45/6.75        ( ( l1_struct_0 @ A ) =>
% 6.45/6.75          ( ![B:$i]:
% 6.45/6.75            ( ( l1_struct_0 @ B ) =>
% 6.45/6.75              ( ![C:$i]:
% 6.45/6.75                ( ( ( v1_funct_1 @ C ) & 
% 6.45/6.75                    ( v1_funct_2 @
% 6.45/6.75                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.45/6.75                    ( m1_subset_1 @
% 6.45/6.75                      C @ 
% 6.45/6.75                      ( k1_zfmisc_1 @
% 6.45/6.75                        ( k2_zfmisc_1 @
% 6.45/6.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.45/6.75                  ( ![D:$i]:
% 6.45/6.75                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.45/6.75                      ( ( ( ( k2_relset_1 @
% 6.45/6.75                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 6.45/6.75                            ( k2_struct_0 @ B ) ) & 
% 6.45/6.75                          ( v2_funct_1 @ C ) ) =>
% 6.45/6.75                        ( ( k7_relset_1 @
% 6.45/6.75                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 6.45/6.75                          ( k8_relset_1 @
% 6.45/6.75                            ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.45/6.75                            ( k2_tops_2 @
% 6.45/6.75                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 6.45/6.75                            D ) ) ) ) ) ) ) ) ) ) )),
% 6.45/6.75    inference('cnf.neg', [status(esa)], [t67_tops_2])).
% 6.45/6.75  thf('3', plain,
% 6.45/6.75      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 6.45/6.75         sk_D)
% 6.45/6.75         != (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.45/6.75             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1) @ 
% 6.45/6.75             sk_D))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('4', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf(redefinition_k7_relset_1, axiom,
% 6.45/6.75    (![A:$i,B:$i,C:$i,D:$i]:
% 6.45/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.45/6.75       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 6.45/6.75  thf('5', plain,
% 6.45/6.75      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 6.45/6.75         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73)))
% 6.45/6.75          | ((k7_relset_1 @ X72 @ X73 @ X71 @ X74) = (k9_relat_1 @ X71 @ X74)))),
% 6.45/6.75      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 6.45/6.75  thf('6', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.45/6.75           sk_C_1 @ X0) = (k9_relat_1 @ sk_C_1 @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['4', '5'])).
% 6.45/6.75  thf('7', plain,
% 6.45/6.75      (((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75         != (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.45/6.75             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1) @ 
% 6.45/6.75             sk_D))),
% 6.45/6.75      inference('demod', [status(thm)], ['3', '6'])).
% 6.45/6.75  thf('8', plain,
% 6.45/6.75      ((((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75          != (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.45/6.75              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1) @ 
% 6.45/6.75              sk_D))
% 6.45/6.75        | ~ (l1_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup-', [status(thm)], ['2', '7'])).
% 6.45/6.75  thf('9', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf('10', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('11', plain,
% 6.45/6.75      (((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75         (k1_zfmisc_1 @ 
% 6.45/6.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 6.45/6.75        | ~ (l1_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup+', [status(thm)], ['9', '10'])).
% 6.45/6.75  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('13', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 6.45/6.75      inference('demod', [status(thm)], ['11', '12'])).
% 6.45/6.75  thf(d4_tops_2, axiom,
% 6.45/6.75    (![A:$i,B:$i,C:$i]:
% 6.45/6.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.45/6.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.45/6.75       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 6.45/6.75         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 6.45/6.75  thf('14', plain,
% 6.45/6.75      (![X85 : $i, X86 : $i, X87 : $i]:
% 6.45/6.75         (((k2_relset_1 @ X86 @ X85 @ X87) != (X85))
% 6.45/6.75          | ~ (v2_funct_1 @ X87)
% 6.45/6.75          | ((k2_tops_2 @ X86 @ X85 @ X87) = (k2_funct_1 @ X87))
% 6.45/6.75          | ~ (m1_subset_1 @ X87 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X85)))
% 6.45/6.75          | ~ (v1_funct_2 @ X87 @ X86 @ X85)
% 6.45/6.75          | ~ (v1_funct_1 @ X87))),
% 6.45/6.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 6.45/6.75  thf('15', plain,
% 6.45/6.75      ((~ (v1_funct_1 @ sk_C_1)
% 6.45/6.75        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 6.45/6.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75            = (k2_funct_1 @ sk_C_1))
% 6.45/6.75        | ~ (v2_funct_1 @ sk_C_1)
% 6.45/6.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75            != (k2_struct_0 @ sk_B)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['13', '14'])).
% 6.45/6.75  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('17', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf('18', plain,
% 6.45/6.75      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('19', plain,
% 6.45/6.75      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 6.45/6.75        | ~ (l1_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup+', [status(thm)], ['17', '18'])).
% 6.45/6.75  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('21', plain,
% 6.45/6.75      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('demod', [status(thm)], ['19', '20'])).
% 6.45/6.75  thf('22', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf(cc2_relat_1, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( v1_relat_1 @ A ) =>
% 6.45/6.75       ( ![B:$i]:
% 6.45/6.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.45/6.75  thf('23', plain,
% 6.45/6.75      (![X45 : $i, X46 : $i]:
% 6.45/6.75         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 6.45/6.75          | (v1_relat_1 @ X45)
% 6.45/6.75          | ~ (v1_relat_1 @ X46))),
% 6.45/6.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.45/6.75  thf('24', plain,
% 6.45/6.75      ((~ (v1_relat_1 @ 
% 6.45/6.75           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 6.45/6.75        | (v1_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('sup-', [status(thm)], ['22', '23'])).
% 6.45/6.75  thf(fc6_relat_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.45/6.75  thf('25', plain,
% 6.45/6.75      (![X48 : $i, X49 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X48 @ X49))),
% 6.45/6.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.45/6.75  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf(d9_funct_1, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.45/6.75       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 6.45/6.75  thf('27', plain,
% 6.45/6.75      (![X57 : $i]:
% 6.45/6.75         (~ (v2_funct_1 @ X57)
% 6.45/6.75          | ((k2_funct_1 @ X57) = (k4_relat_1 @ X57))
% 6.45/6.75          | ~ (v1_funct_1 @ X57)
% 6.45/6.75          | ~ (v1_relat_1 @ X57))),
% 6.45/6.75      inference('cnf', [status(esa)], [d9_funct_1])).
% 6.45/6.75  thf('28', plain,
% 6.45/6.75      ((~ (v1_funct_1 @ sk_C_1)
% 6.45/6.75        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | ~ (v2_funct_1 @ sk_C_1))),
% 6.45/6.75      inference('sup-', [status(thm)], ['26', '27'])).
% 6.45/6.75  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('30', plain, ((v2_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('31', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 6.45/6.75  thf('32', plain, ((v2_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('33', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf('34', plain,
% 6.45/6.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75         = (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('35', plain,
% 6.45/6.75      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75          = (k2_struct_0 @ sk_B))
% 6.45/6.75        | ~ (l1_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup+', [status(thm)], ['33', '34'])).
% 6.45/6.75  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('37', plain,
% 6.45/6.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75         = (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('demod', [status(thm)], ['35', '36'])).
% 6.45/6.75  thf('38', plain,
% 6.45/6.75      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75          = (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 6.45/6.75      inference('demod', [status(thm)], ['15', '16', '21', '31', '32', '37'])).
% 6.45/6.75  thf('39', plain,
% 6.45/6.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75         = (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('simplify', [status(thm)], ['38'])).
% 6.45/6.75  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('41', plain,
% 6.45/6.75      (((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75         != (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.45/6.75             (k4_relat_1 @ sk_C_1) @ sk_D))),
% 6.45/6.75      inference('demod', [status(thm)], ['8', '39', '40'])).
% 6.45/6.75  thf('42', plain,
% 6.45/6.75      ((((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75          != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.45/6.75              (k4_relat_1 @ sk_C_1) @ sk_D))
% 6.45/6.75        | ~ (l1_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup-', [status(thm)], ['1', '41'])).
% 6.45/6.75  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('44', plain,
% 6.45/6.75      (((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75         != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.45/6.75             (k4_relat_1 @ sk_C_1) @ sk_D))),
% 6.45/6.75      inference('demod', [status(thm)], ['42', '43'])).
% 6.45/6.75  thf('45', plain,
% 6.45/6.75      ((((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75          != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.45/6.75              (k4_relat_1 @ sk_C_1) @ sk_D))
% 6.45/6.75        | ~ (l1_struct_0 @ sk_A))),
% 6.45/6.75      inference('sup-', [status(thm)], ['0', '44'])).
% 6.45/6.75  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('47', plain,
% 6.45/6.75      (((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75         != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.45/6.75             (k4_relat_1 @ sk_C_1) @ sk_D))),
% 6.45/6.75      inference('demod', [status(thm)], ['45', '46'])).
% 6.45/6.75  thf('48', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 6.45/6.75  thf(t55_funct_1, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.45/6.75       ( ( v2_funct_1 @ A ) =>
% 6.45/6.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.45/6.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.45/6.75  thf('49', plain,
% 6.45/6.75      (![X63 : $i]:
% 6.45/6.75         (~ (v2_funct_1 @ X63)
% 6.45/6.75          | ((k2_relat_1 @ X63) = (k1_relat_1 @ (k2_funct_1 @ X63)))
% 6.45/6.75          | ~ (v1_funct_1 @ X63)
% 6.45/6.75          | ~ (v1_relat_1 @ X63))),
% 6.45/6.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.45/6.75  thf('50', plain,
% 6.45/6.75      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 6.45/6.75        | ~ (v1_relat_1 @ sk_C_1)
% 6.45/6.75        | ~ (v1_funct_1 @ sk_C_1)
% 6.45/6.75        | ~ (v2_funct_1 @ sk_C_1))),
% 6.45/6.75      inference('sup+', [status(thm)], ['48', '49'])).
% 6.45/6.75  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('53', plain, ((v2_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('54', plain,
% 6.45/6.75      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 6.45/6.75  thf(t21_relat_1, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( v1_relat_1 @ A ) =>
% 6.45/6.75       ( r1_tarski @
% 6.45/6.75         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 6.45/6.75  thf('55', plain,
% 6.45/6.75      (![X56 : $i]:
% 6.45/6.75         ((r1_tarski @ X56 @ 
% 6.45/6.75           (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 6.45/6.75          | ~ (v1_relat_1 @ X56))),
% 6.45/6.75      inference('cnf', [status(esa)], [t21_relat_1])).
% 6.45/6.75  thf('56', plain,
% 6.45/6.75      (((r1_tarski @ (k4_relat_1 @ sk_C_1) @ 
% 6.45/6.75         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C_1) @ 
% 6.45/6.75          (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))
% 6.45/6.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['54', '55'])).
% 6.45/6.75  thf('57', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 6.45/6.75  thf('58', plain,
% 6.45/6.75      (![X63 : $i]:
% 6.45/6.75         (~ (v2_funct_1 @ X63)
% 6.45/6.75          | ((k1_relat_1 @ X63) = (k2_relat_1 @ (k2_funct_1 @ X63)))
% 6.45/6.75          | ~ (v1_funct_1 @ X63)
% 6.45/6.75          | ~ (v1_relat_1 @ X63))),
% 6.45/6.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.45/6.75  thf('59', plain,
% 6.45/6.75      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 6.45/6.75        | ~ (v1_relat_1 @ sk_C_1)
% 6.45/6.75        | ~ (v1_funct_1 @ sk_C_1)
% 6.45/6.75        | ~ (v2_funct_1 @ sk_C_1))),
% 6.45/6.75      inference('sup+', [status(thm)], ['57', '58'])).
% 6.45/6.75  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('62', plain, ((v2_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('63', plain,
% 6.45/6.75      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 6.45/6.75  thf('64', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 6.45/6.75  thf(dt_k2_funct_1, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.45/6.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.45/6.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.45/6.75  thf('65', plain,
% 6.45/6.75      (![X58 : $i]:
% 6.45/6.75         ((v1_relat_1 @ (k2_funct_1 @ X58))
% 6.45/6.75          | ~ (v1_funct_1 @ X58)
% 6.45/6.75          | ~ (v1_relat_1 @ X58))),
% 6.45/6.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.45/6.75  thf('66', plain,
% 6.45/6.75      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | ~ (v1_relat_1 @ sk_C_1)
% 6.45/6.75        | ~ (v1_funct_1 @ sk_C_1))),
% 6.45/6.75      inference('sup+', [status(thm)], ['64', '65'])).
% 6.45/6.75  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('69', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.45/6.75  thf('70', plain,
% 6.45/6.75      ((r1_tarski @ (k4_relat_1 @ sk_C_1) @ 
% 6.45/6.75        (k2_zfmisc_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['56', '63', '69'])).
% 6.45/6.75  thf('71', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf(redefinition_k2_relset_1, axiom,
% 6.45/6.75    (![A:$i,B:$i,C:$i]:
% 6.45/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.45/6.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.45/6.75  thf('72', plain,
% 6.45/6.75      (![X68 : $i, X69 : $i, X70 : $i]:
% 6.45/6.75         (((k2_relset_1 @ X69 @ X70 @ X68) = (k2_relat_1 @ X68))
% 6.45/6.75          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70))))),
% 6.45/6.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.45/6.75  thf('73', plain,
% 6.45/6.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75         = (k2_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('sup-', [status(thm)], ['71', '72'])).
% 6.45/6.75  thf('74', plain,
% 6.45/6.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 6.45/6.75         = (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('75', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup+', [status(thm)], ['73', '74'])).
% 6.45/6.75  thf('76', plain,
% 6.45/6.75      ((r1_tarski @ (k4_relat_1 @ sk_C_1) @ 
% 6.45/6.75        (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['70', '75'])).
% 6.45/6.75  thf(t3_subset, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.45/6.75  thf('77', plain,
% 6.45/6.75      (![X39 : $i, X41 : $i]:
% 6.45/6.75         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 6.45/6.75      inference('cnf', [status(esa)], [t3_subset])).
% 6.45/6.75  thf('78', plain,
% 6.45/6.75      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C_1))))),
% 6.45/6.75      inference('sup-', [status(thm)], ['76', '77'])).
% 6.45/6.75  thf(redefinition_k8_relset_1, axiom,
% 6.45/6.75    (![A:$i,B:$i,C:$i,D:$i]:
% 6.45/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.45/6.75       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 6.45/6.75  thf('79', plain,
% 6.45/6.75      (![X75 : $i, X76 : $i, X77 : $i, X78 : $i]:
% 6.45/6.75         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X76 @ X77)))
% 6.45/6.75          | ((k8_relset_1 @ X76 @ X77 @ X75 @ X78) = (k10_relat_1 @ X75 @ X78)))),
% 6.45/6.75      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 6.45/6.75  thf('80', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((k8_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C_1) @ 
% 6.45/6.75           (k4_relat_1 @ sk_C_1) @ X0)
% 6.45/6.75           = (k10_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['78', '79'])).
% 6.45/6.75  thf('81', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['28', '29', '30'])).
% 6.45/6.75  thf(t154_funct_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.45/6.75       ( ( v2_funct_1 @ B ) =>
% 6.45/6.75         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 6.45/6.75  thf('82', plain,
% 6.45/6.75      (![X61 : $i, X62 : $i]:
% 6.45/6.75         (~ (v2_funct_1 @ X61)
% 6.45/6.75          | ((k9_relat_1 @ X61 @ X62)
% 6.45/6.75              = (k10_relat_1 @ (k2_funct_1 @ X61) @ X62))
% 6.45/6.75          | ~ (v1_funct_1 @ X61)
% 6.45/6.75          | ~ (v1_relat_1 @ X61))),
% 6.45/6.75      inference('cnf', [status(esa)], [t154_funct_1])).
% 6.45/6.75  thf('83', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k9_relat_1 @ sk_C_1 @ X0)
% 6.45/6.75            = (k10_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))
% 6.45/6.75          | ~ (v1_relat_1 @ sk_C_1)
% 6.45/6.75          | ~ (v1_funct_1 @ sk_C_1)
% 6.45/6.75          | ~ (v2_funct_1 @ sk_C_1))),
% 6.45/6.75      inference('sup+', [status(thm)], ['81', '82'])).
% 6.45/6.75  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('85', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('86', plain, ((v2_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('87', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((k9_relat_1 @ sk_C_1 @ X0)
% 6.45/6.75           = (k10_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 6.45/6.75  thf('88', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((k8_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C_1) @ 
% 6.45/6.75           (k4_relat_1 @ sk_C_1) @ X0) = (k9_relat_1 @ sk_C_1 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['80', '87'])).
% 6.45/6.75  thf('89', plain,
% 6.45/6.75      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C_1))))),
% 6.45/6.75      inference('sup-', [status(thm)], ['76', '77'])).
% 6.45/6.75  thf(cc2_relset_1, axiom,
% 6.45/6.75    (![A:$i,B:$i,C:$i]:
% 6.45/6.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.45/6.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.45/6.75  thf('90', plain,
% 6.45/6.75      (![X65 : $i, X66 : $i, X67 : $i]:
% 6.45/6.75         ((v4_relat_1 @ X65 @ X66)
% 6.45/6.75          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 6.45/6.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.45/6.75  thf('91', plain,
% 6.45/6.75      ((v4_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup-', [status(thm)], ['89', '90'])).
% 6.45/6.75  thf(t209_relat_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 6.45/6.75       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 6.45/6.75  thf('92', plain,
% 6.45/6.75      (![X54 : $i, X55 : $i]:
% 6.45/6.75         (((X54) = (k7_relat_1 @ X54 @ X55))
% 6.45/6.75          | ~ (v4_relat_1 @ X54 @ X55)
% 6.45/6.75          | ~ (v1_relat_1 @ X54))),
% 6.45/6.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.45/6.75  thf('93', plain,
% 6.45/6.75      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | ((k4_relat_1 @ sk_C_1)
% 6.45/6.75            = (k7_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))))),
% 6.45/6.75      inference('sup-', [status(thm)], ['91', '92'])).
% 6.45/6.75  thf('94', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.45/6.75  thf('95', plain,
% 6.45/6.75      (((k4_relat_1 @ sk_C_1)
% 6.45/6.75         = (k7_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 6.45/6.75      inference('demod', [status(thm)], ['93', '94'])).
% 6.45/6.75  thf(t148_relat_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( v1_relat_1 @ B ) =>
% 6.45/6.75       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 6.45/6.75  thf('96', plain,
% 6.45/6.75      (![X50 : $i, X51 : $i]:
% 6.45/6.75         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 6.45/6.75          | ~ (v1_relat_1 @ X50))),
% 6.45/6.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.45/6.75  thf('97', plain,
% 6.45/6.75      ((((k2_relat_1 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75          = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 6.45/6.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['95', '96'])).
% 6.45/6.75  thf('98', plain,
% 6.45/6.75      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 6.45/6.75  thf('99', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.45/6.75  thf('100', plain,
% 6.45/6.75      (((k1_relat_1 @ sk_C_1)
% 6.45/6.75         = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 6.45/6.75      inference('demod', [status(thm)], ['97', '98', '99'])).
% 6.45/6.75  thf('101', plain,
% 6.45/6.75      (![X84 : $i]:
% 6.45/6.75         (((k2_struct_0 @ X84) = (u1_struct_0 @ X84)) | ~ (l1_struct_0 @ X84))),
% 6.45/6.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.45/6.75  thf(l13_xboole_0, axiom,
% 6.45/6.75    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.45/6.75  thf('102', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf(t4_subset_1, axiom,
% 6.45/6.75    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.45/6.75  thf('103', plain,
% 6.45/6.75      (![X38 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 6.45/6.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.45/6.75  thf('104', plain,
% 6.45/6.75      (![X65 : $i, X66 : $i, X67 : $i]:
% 6.45/6.75         ((v4_relat_1 @ X65 @ X66)
% 6.45/6.75          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 6.45/6.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.45/6.75  thf('105', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 6.45/6.75      inference('sup-', [status(thm)], ['103', '104'])).
% 6.45/6.75  thf('106', plain,
% 6.45/6.75      (![X54 : $i, X55 : $i]:
% 6.45/6.75         (((X54) = (k7_relat_1 @ X54 @ X55))
% 6.45/6.75          | ~ (v4_relat_1 @ X54 @ X55)
% 6.45/6.75          | ~ (v1_relat_1 @ X54))),
% 6.45/6.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.45/6.75  thf('107', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_relat_1 @ k1_xboole_0)
% 6.45/6.75          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['105', '106'])).
% 6.45/6.75  thf(t45_ordinal1, axiom,
% 6.45/6.75    (![A:$i]:
% 6.45/6.75     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 6.45/6.75       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 6.45/6.75  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.45/6.75      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.45/6.75  thf('109', plain,
% 6.45/6.75      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['107', '108'])).
% 6.45/6.75  thf('110', plain,
% 6.45/6.75      (![X50 : $i, X51 : $i]:
% 6.45/6.75         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 6.45/6.75          | ~ (v1_relat_1 @ X50))),
% 6.45/6.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.45/6.75  thf('111', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 6.45/6.75          | ~ (v1_relat_1 @ k1_xboole_0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['109', '110'])).
% 6.45/6.75  thf(t60_relat_1, axiom,
% 6.45/6.75    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.45/6.75     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.45/6.75  thf('112', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.45/6.75  thf('113', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.45/6.75      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.45/6.75  thf('114', plain,
% 6.45/6.75      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['111', '112', '113'])).
% 6.45/6.75  thf('115', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (((k1_xboole_0) = (k9_relat_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['102', '114'])).
% 6.45/6.75  thf(t3_xboole_0, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 6.45/6.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.45/6.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.45/6.75            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 6.45/6.75  thf('116', plain,
% 6.45/6.75      (![X1 : $i, X2 : $i]:
% 6.45/6.75         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 6.45/6.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.45/6.75  thf('117', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.45/6.75  thf(t142_funct_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( v1_relat_1 @ B ) =>
% 6.45/6.75       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 6.45/6.75         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 6.45/6.75  thf('118', plain,
% 6.45/6.75      (![X59 : $i, X60 : $i]:
% 6.45/6.75         (~ (r2_hidden @ X60 @ (k2_relat_1 @ X59))
% 6.45/6.75          | ((k10_relat_1 @ X59 @ (k1_tarski @ X60)) != (k1_xboole_0))
% 6.45/6.75          | ~ (v1_relat_1 @ X59))),
% 6.45/6.75      inference('cnf', [status(esa)], [t142_funct_1])).
% 6.45/6.75  thf('119', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 6.45/6.75          | ~ (v1_relat_1 @ k1_xboole_0)
% 6.45/6.75          | ((k10_relat_1 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_xboole_0)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['117', '118'])).
% 6.45/6.75  thf('120', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.45/6.75      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.45/6.75  thf(t172_relat_1, axiom,
% 6.45/6.75    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 6.45/6.75  thf('121', plain,
% 6.45/6.75      (![X53 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X53) = (k1_xboole_0))),
% 6.45/6.75      inference('cnf', [status(esa)], [t172_relat_1])).
% 6.45/6.75  thf('122', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 6.45/6.75      inference('demod', [status(thm)], ['119', '120', '121'])).
% 6.45/6.75  thf('123', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.45/6.75      inference('simplify', [status(thm)], ['122'])).
% 6.45/6.75  thf('124', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 6.45/6.75      inference('sup-', [status(thm)], ['116', '123'])).
% 6.45/6.75  thf(t69_xboole_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.45/6.75       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 6.45/6.75  thf('125', plain,
% 6.45/6.75      (![X5 : $i, X6 : $i]:
% 6.45/6.75         (~ (r1_xboole_0 @ X5 @ X6)
% 6.45/6.75          | ~ (r1_tarski @ X5 @ X6)
% 6.45/6.75          | (v1_xboole_0 @ X5))),
% 6.45/6.75      inference('cnf', [status(esa)], [t69_xboole_1])).
% 6.45/6.75  thf('126', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['124', '125'])).
% 6.45/6.75  thf('127', plain,
% 6.45/6.75      (![X38 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 6.45/6.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.45/6.75  thf('128', plain,
% 6.45/6.75      (![X39 : $i, X40 : $i]:
% 6.45/6.75         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 6.45/6.75      inference('cnf', [status(esa)], [t3_subset])).
% 6.45/6.75  thf('129', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.45/6.75      inference('sup-', [status(thm)], ['127', '128'])).
% 6.45/6.75  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.45/6.75      inference('demod', [status(thm)], ['126', '129'])).
% 6.45/6.75  thf('131', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 6.45/6.75      inference('sup+', [status(thm)], ['115', '130'])).
% 6.45/6.75  thf('132', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf(t132_funct_2, axiom,
% 6.45/6.75    (![A:$i,B:$i,C:$i]:
% 6.45/6.75     ( ( ( v1_funct_1 @ C ) & 
% 6.45/6.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.45/6.75       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.45/6.75           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.45/6.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 6.45/6.75           ( v1_partfun1 @ C @ A ) ) ) ))).
% 6.45/6.75  thf('133', plain,
% 6.45/6.75      (![X81 : $i, X82 : $i, X83 : $i]:
% 6.45/6.75         (((X81) = (k1_xboole_0))
% 6.45/6.75          | ~ (v1_funct_1 @ X82)
% 6.45/6.75          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X81)))
% 6.45/6.75          | (v1_partfun1 @ X82 @ X83)
% 6.45/6.75          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X81)))
% 6.45/6.75          | ~ (v1_funct_2 @ X82 @ X83 @ X81)
% 6.45/6.75          | ~ (v1_funct_1 @ X82))),
% 6.45/6.75      inference('cnf', [status(esa)], [t132_funct_2])).
% 6.45/6.75  thf('134', plain,
% 6.45/6.75      (![X81 : $i, X82 : $i, X83 : $i]:
% 6.45/6.75         (~ (v1_funct_2 @ X82 @ X83 @ X81)
% 6.45/6.75          | (v1_partfun1 @ X82 @ X83)
% 6.45/6.75          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X81)))
% 6.45/6.75          | ~ (v1_funct_1 @ X82)
% 6.45/6.75          | ((X81) = (k1_xboole_0)))),
% 6.45/6.75      inference('simplify', [status(thm)], ['133'])).
% 6.45/6.75  thf('135', plain,
% 6.45/6.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.45/6.75        | ~ (v1_funct_1 @ sk_C_1)
% 6.45/6.75        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 6.45/6.75        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['132', '134'])).
% 6.45/6.75  thf('136', plain, ((v1_funct_1 @ sk_C_1)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('137', plain,
% 6.45/6.75      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('138', plain,
% 6.45/6.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.45/6.75        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('demod', [status(thm)], ['135', '136', '137'])).
% 6.45/6.75  thf(d4_partfun1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 6.45/6.75       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 6.45/6.75  thf('139', plain,
% 6.45/6.75      (![X79 : $i, X80 : $i]:
% 6.45/6.75         (~ (v1_partfun1 @ X80 @ X79)
% 6.45/6.75          | ((k1_relat_1 @ X80) = (X79))
% 6.45/6.75          | ~ (v4_relat_1 @ X80 @ X79)
% 6.45/6.75          | ~ (v1_relat_1 @ X80))),
% 6.45/6.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 6.45/6.75  thf('140', plain,
% 6.45/6.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.45/6.75        | ~ (v1_relat_1 @ sk_C_1)
% 6.45/6.75        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['138', '139'])).
% 6.45/6.75  thf('141', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('142', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('143', plain,
% 6.45/6.75      (![X65 : $i, X66 : $i, X67 : $i]:
% 6.45/6.75         ((v4_relat_1 @ X65 @ X66)
% 6.45/6.75          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 6.45/6.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.45/6.75  thf('144', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 6.45/6.75      inference('sup-', [status(thm)], ['142', '143'])).
% 6.45/6.75  thf('145', plain,
% 6.45/6.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('demod', [status(thm)], ['140', '141', '144'])).
% 6.45/6.75  thf('146', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('147', plain,
% 6.45/6.75      (((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['145', '146'])).
% 6.45/6.75  thf(t113_zfmisc_1, axiom,
% 6.45/6.75    (![A:$i,B:$i]:
% 6.45/6.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.45/6.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.45/6.75  thf('148', plain,
% 6.45/6.75      (![X36 : $i, X37 : $i]:
% 6.45/6.75         (((k2_zfmisc_1 @ X36 @ X37) = (k1_xboole_0))
% 6.45/6.75          | ((X37) != (k1_xboole_0)))),
% 6.45/6.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.45/6.75  thf('149', plain,
% 6.45/6.75      (![X36 : $i]: ((k2_zfmisc_1 @ X36 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('simplify', [status(thm)], ['148'])).
% 6.45/6.75  thf('150', plain,
% 6.45/6.75      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('demod', [status(thm)], ['147', '149'])).
% 6.45/6.75  thf('151', plain,
% 6.45/6.75      (![X36 : $i]: ((k2_zfmisc_1 @ X36 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('simplify', [status(thm)], ['148'])).
% 6.45/6.75  thf('152', plain,
% 6.45/6.75      (![X65 : $i, X66 : $i, X67 : $i]:
% 6.45/6.75         ((v4_relat_1 @ X65 @ X66)
% 6.45/6.75          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 6.45/6.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.45/6.75  thf('153', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.45/6.75          | (v4_relat_1 @ X1 @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['151', '152'])).
% 6.45/6.75  thf('154', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75          | (v4_relat_1 @ sk_C_1 @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['150', '153'])).
% 6.45/6.75  thf('155', plain,
% 6.45/6.75      (![X54 : $i, X55 : $i]:
% 6.45/6.75         (((X54) = (k7_relat_1 @ X54 @ X55))
% 6.45/6.75          | ~ (v4_relat_1 @ X54 @ X55)
% 6.45/6.75          | ~ (v1_relat_1 @ X54))),
% 6.45/6.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.45/6.75  thf('156', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75          | ~ (v1_relat_1 @ sk_C_1)
% 6.45/6.75          | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ X0)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['154', '155'])).
% 6.45/6.75  thf('157', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('158', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75          | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ X0)))),
% 6.45/6.75      inference('demod', [status(thm)], ['156', '157'])).
% 6.45/6.75  thf('159', plain,
% 6.45/6.75      (![X50 : $i, X51 : $i]:
% 6.45/6.75         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 6.45/6.75          | ~ (v1_relat_1 @ X50))),
% 6.45/6.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.45/6.75  thf('160', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ X0))
% 6.45/6.75          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75          | ~ (v1_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('sup+', [status(thm)], ['158', '159'])).
% 6.45/6.75  thf('161', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup+', [status(thm)], ['73', '74'])).
% 6.45/6.75  thf('162', plain, ((v1_relat_1 @ sk_C_1)),
% 6.45/6.75      inference('demod', [status(thm)], ['24', '25'])).
% 6.45/6.75  thf('163', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k2_struct_0 @ sk_B) = (k9_relat_1 @ sk_C_1 @ X0))
% 6.45/6.75          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('demod', [status(thm)], ['160', '161', '162'])).
% 6.45/6.75  thf('164', plain,
% 6.45/6.75      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 6.45/6.75  thf('165', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 6.45/6.75      inference('sup+', [status(thm)], ['73', '74'])).
% 6.45/6.75  thf('166', plain,
% 6.45/6.75      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['164', '165'])).
% 6.45/6.75  thf('167', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('168', plain,
% 6.45/6.75      (![X36 : $i, X37 : $i]:
% 6.45/6.75         (((k2_zfmisc_1 @ X36 @ X37) = (k1_xboole_0))
% 6.45/6.75          | ((X36) != (k1_xboole_0)))),
% 6.45/6.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.45/6.75  thf('169', plain,
% 6.45/6.75      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 6.45/6.75      inference('simplify', [status(thm)], ['168'])).
% 6.45/6.75  thf('170', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['167', '169'])).
% 6.45/6.75  thf('171', plain,
% 6.45/6.75      (![X56 : $i]:
% 6.45/6.75         ((r1_tarski @ X56 @ 
% 6.45/6.75           (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 6.45/6.75          | ~ (v1_relat_1 @ X56))),
% 6.45/6.75      inference('cnf', [status(esa)], [t21_relat_1])).
% 6.45/6.75  thf('172', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('173', plain,
% 6.45/6.75      (![X1 : $i, X2 : $i]:
% 6.45/6.75         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X2))),
% 6.45/6.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.45/6.75  thf('174', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.45/6.75      inference('simplify', [status(thm)], ['122'])).
% 6.45/6.75  thf('175', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.45/6.75      inference('sup-', [status(thm)], ['173', '174'])).
% 6.45/6.75  thf('176', plain,
% 6.45/6.75      (![X5 : $i, X6 : $i]:
% 6.45/6.75         (~ (r1_xboole_0 @ X5 @ X6)
% 6.45/6.75          | ~ (r1_tarski @ X5 @ X6)
% 6.45/6.75          | (v1_xboole_0 @ X5))),
% 6.45/6.75      inference('cnf', [status(esa)], [t69_xboole_1])).
% 6.45/6.75  thf('177', plain,
% 6.45/6.75      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['175', '176'])).
% 6.45/6.75  thf('178', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (~ (r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1))),
% 6.45/6.75      inference('sup-', [status(thm)], ['172', '177'])).
% 6.45/6.75  thf('179', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_relat_1 @ X0)
% 6.45/6.75          | (v1_xboole_0 @ X0)
% 6.45/6.75          | ~ (v1_xboole_0 @ 
% 6.45/6.75               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 6.45/6.75      inference('sup-', [status(thm)], ['171', '178'])).
% 6.45/6.75  thf('180', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.45/6.75          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 6.45/6.75          | (v1_xboole_0 @ X0)
% 6.45/6.75          | ~ (v1_relat_1 @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['170', '179'])).
% 6.45/6.75  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.45/6.75      inference('demod', [status(thm)], ['126', '129'])).
% 6.45/6.75  thf('182', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 6.45/6.75          | (v1_xboole_0 @ X0)
% 6.45/6.75          | ~ (v1_relat_1 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['180', '181'])).
% 6.45/6.75  thf('183', plain,
% 6.45/6.75      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 6.45/6.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['166', '182'])).
% 6.45/6.75  thf('184', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.45/6.75  thf('185', plain,
% 6.45/6.75      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['183', '184'])).
% 6.45/6.75  thf('186', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_xboole_0 @ (k9_relat_1 @ sk_C_1 @ X0))
% 6.45/6.75          | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75          | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['163', '185'])).
% 6.45/6.75  thf('187', plain,
% 6.45/6.75      ((~ (v1_xboole_0 @ sk_C_1)
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['131', '186'])).
% 6.45/6.75  thf('188', plain,
% 6.45/6.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('demod', [status(thm)], ['140', '141', '144'])).
% 6.45/6.75  thf('189', plain,
% 6.45/6.75      ((m1_subset_1 @ sk_C_1 @ 
% 6.45/6.75        (k1_zfmisc_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('190', plain,
% 6.45/6.75      (![X39 : $i, X40 : $i]:
% 6.45/6.75         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 6.45/6.75      inference('cnf', [status(esa)], [t3_subset])).
% 6.45/6.75  thf('191', plain,
% 6.45/6.75      ((r1_tarski @ sk_C_1 @ 
% 6.45/6.75        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['189', '190'])).
% 6.45/6.75  thf('192', plain,
% 6.45/6.75      (((r1_tarski @ sk_C_1 @ 
% 6.45/6.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['188', '191'])).
% 6.45/6.75  thf('193', plain,
% 6.45/6.75      (![X36 : $i]: ((k2_zfmisc_1 @ X36 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('simplify', [status(thm)], ['148'])).
% 6.45/6.75  thf('194', plain,
% 6.45/6.75      (((r1_tarski @ sk_C_1 @ k1_xboole_0)
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 6.45/6.75      inference('demod', [status(thm)], ['192', '193'])).
% 6.45/6.75  thf('195', plain,
% 6.45/6.75      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['175', '176'])).
% 6.45/6.75  thf('196', plain,
% 6.45/6.75      ((((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 6.45/6.75      inference('sup-', [status(thm)], ['194', '195'])).
% 6.45/6.75  thf('197', plain,
% 6.45/6.75      ((((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('clc', [status(thm)], ['187', '196'])).
% 6.45/6.75  thf('198', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('199', plain,
% 6.45/6.75      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['107', '108'])).
% 6.45/6.75  thf('200', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (((k1_xboole_0) = (k7_relat_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['198', '199'])).
% 6.45/6.75  thf('201', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))
% 6.45/6.75          | ((k1_xboole_0) = (k7_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['197', '200'])).
% 6.45/6.75  thf('202', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 6.45/6.75          | ~ (l1_struct_0 @ sk_A)
% 6.45/6.75          | ((k1_xboole_0) = (k7_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['101', '201'])).
% 6.45/6.75  thf('203', plain, ((l1_struct_0 @ sk_A)),
% 6.45/6.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.45/6.75  thf('204', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 6.45/6.75          | ((k1_xboole_0) = (k7_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0)))),
% 6.45/6.75      inference('demod', [status(thm)], ['202', '203'])).
% 6.45/6.75  thf('205', plain,
% 6.45/6.75      (![X50 : $i, X51 : $i]:
% 6.45/6.75         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 6.45/6.75          | ~ (v1_relat_1 @ X50))),
% 6.45/6.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.45/6.75  thf('206', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('207', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.45/6.75  thf('208', plain,
% 6.45/6.75      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['206', '207'])).
% 6.45/6.75  thf('209', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.45/6.75      inference('demod', [status(thm)], ['126', '129'])).
% 6.45/6.75  thf('210', plain,
% 6.45/6.75      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['208', '209'])).
% 6.45/6.75  thf('211', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 6.45/6.75          | ~ (v1_relat_1 @ X1)
% 6.45/6.75          | ~ (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['205', '210'])).
% 6.45/6.75  thf('212', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.45/6.75          | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 6.45/6.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75          | (v1_xboole_0 @ (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['204', '211'])).
% 6.45/6.75  thf('213', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.45/6.75      inference('demod', [status(thm)], ['126', '129'])).
% 6.45/6.75  thf('214', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.45/6.75  thf('215', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 6.45/6.75          | (v1_xboole_0 @ (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0)))),
% 6.45/6.75      inference('demod', [status(thm)], ['212', '213', '214'])).
% 6.45/6.75  thf('216', plain,
% 6.45/6.75      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 6.45/6.75        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['100', '215'])).
% 6.45/6.75  thf('217', plain,
% 6.45/6.75      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 6.45/6.75  thf('218', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('219', plain,
% 6.45/6.75      (![X36 : $i]: ((k2_zfmisc_1 @ X36 @ k1_xboole_0) = (k1_xboole_0))),
% 6.45/6.75      inference('simplify', [status(thm)], ['148'])).
% 6.45/6.75  thf('220', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['218', '219'])).
% 6.45/6.75  thf('221', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_relat_1 @ X0)
% 6.45/6.75          | (v1_xboole_0 @ X0)
% 6.45/6.75          | ~ (v1_xboole_0 @ 
% 6.45/6.75               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 6.45/6.75      inference('sup-', [status(thm)], ['171', '178'])).
% 6.45/6.75  thf('222', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.45/6.75          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 6.45/6.75          | (v1_xboole_0 @ X0)
% 6.45/6.75          | ~ (v1_relat_1 @ X0))),
% 6.45/6.75      inference('sup-', [status(thm)], ['220', '221'])).
% 6.45/6.75  thf('223', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.45/6.75      inference('demod', [status(thm)], ['126', '129'])).
% 6.45/6.75  thf('224', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 6.45/6.75          | (v1_xboole_0 @ X0)
% 6.45/6.75          | ~ (v1_relat_1 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['222', '223'])).
% 6.45/6.75  thf('225', plain,
% 6.45/6.75      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 6.45/6.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['217', '224'])).
% 6.45/6.75  thf('226', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.45/6.75  thf('227', plain,
% 6.45/6.75      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('demod', [status(thm)], ['225', '226'])).
% 6.45/6.75  thf('228', plain,
% 6.45/6.75      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 6.45/6.75        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['216', '227'])).
% 6.45/6.75  thf('229', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('230', plain,
% 6.45/6.75      (![X38 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 6.45/6.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.45/6.75  thf('231', plain,
% 6.45/6.75      (![X75 : $i, X76 : $i, X77 : $i, X78 : $i]:
% 6.45/6.75         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X76 @ X77)))
% 6.45/6.75          | ((k8_relset_1 @ X76 @ X77 @ X75 @ X78) = (k10_relat_1 @ X75 @ X78)))),
% 6.45/6.75      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 6.45/6.75  thf('232', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.45/6.75         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 6.45/6.75           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 6.45/6.75      inference('sup-', [status(thm)], ['230', '231'])).
% 6.45/6.75  thf('233', plain,
% 6.45/6.75      (![X53 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X53) = (k1_xboole_0))),
% 6.45/6.75      inference('cnf', [status(esa)], [t172_relat_1])).
% 6.45/6.75  thf('234', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.45/6.75         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 6.45/6.75      inference('demod', [status(thm)], ['232', '233'])).
% 6.45/6.75  thf('235', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.45/6.75         (((k8_relset_1 @ X3 @ X2 @ X0 @ X1) = (k1_xboole_0))
% 6.45/6.75          | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['229', '234'])).
% 6.45/6.75  thf('236', plain,
% 6.45/6.75      (((k9_relat_1 @ sk_C_1 @ sk_D)
% 6.45/6.75         != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.45/6.75             (k4_relat_1 @ sk_C_1) @ sk_D))),
% 6.45/6.75      inference('demod', [status(thm)], ['45', '46'])).
% 6.45/6.75  thf('237', plain,
% 6.45/6.75      ((((k9_relat_1 @ sk_C_1 @ sk_D) != (k1_xboole_0))
% 6.45/6.75        | ~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup-', [status(thm)], ['235', '236'])).
% 6.45/6.75  thf('238', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((k9_relat_1 @ sk_C_1 @ X0)
% 6.45/6.75           = (k10_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 6.45/6.75  thf('239', plain,
% 6.45/6.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.45/6.75  thf('240', plain,
% 6.45/6.75      (![X53 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X53) = (k1_xboole_0))),
% 6.45/6.75      inference('cnf', [status(esa)], [t172_relat_1])).
% 6.45/6.75  thf('241', plain,
% 6.45/6.75      (![X0 : $i, X1 : $i]:
% 6.45/6.75         (((k10_relat_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.45/6.75      inference('sup+', [status(thm)], ['239', '240'])).
% 6.45/6.75  thf('242', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         (((k9_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 6.45/6.75          | ~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 6.45/6.75      inference('sup+', [status(thm)], ['238', '241'])).
% 6.45/6.75  thf('243', plain, (~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))),
% 6.45/6.75      inference('clc', [status(thm)], ['237', '242'])).
% 6.45/6.75  thf('244', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 6.45/6.75      inference('sup-', [status(thm)], ['228', '243'])).
% 6.45/6.75  thf('245', plain,
% 6.45/6.75      (![X0 : $i]:
% 6.45/6.75         ((k8_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.45/6.75           (k4_relat_1 @ sk_C_1) @ X0) = (k9_relat_1 @ sk_C_1 @ X0))),
% 6.45/6.75      inference('demod', [status(thm)], ['88', '244'])).
% 6.45/6.75  thf('246', plain,
% 6.45/6.75      (((k9_relat_1 @ sk_C_1 @ sk_D) != (k9_relat_1 @ sk_C_1 @ sk_D))),
% 6.45/6.75      inference('demod', [status(thm)], ['47', '245'])).
% 6.45/6.75  thf('247', plain, ($false), inference('simplify', [status(thm)], ['246'])).
% 6.45/6.75  
% 6.45/6.75  % SZS output end Refutation
% 6.45/6.75  
% 6.59/6.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
