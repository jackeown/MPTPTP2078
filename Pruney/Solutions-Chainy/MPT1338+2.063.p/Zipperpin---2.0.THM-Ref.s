%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NNISplSDOu

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  299 (10357 expanded)
%              Number of leaves         :   43 (2981 expanded)
%              Depth                    :   31
%              Number of atoms          : 2686 (262224 expanded)
%              Number of equality atoms :  166 (13175 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('1',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k10_relat_1 @ X7 @ X8 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X7 ) @ X8 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( ( k9_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('12',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('62',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','64'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','64'])).

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

thf('83',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('89',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','101'])).

thf('103',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','81','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('108',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','108'])).

thf('110',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116','119'])).

thf('121',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('123',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('129',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('132',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','132'])).

thf('134',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['120','138'])).

thf('140',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('141',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('144',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('148',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['142','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('151',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('156',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X31 @ X32 @ X33 ) @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('160',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['137'])).

thf('162',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','154','162'])).

thf('164',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('166',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('167',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('168',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('170',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['167','170'])).

thf('172',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['164','171'])).

thf('173',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['163','176'])).

thf('178',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('179',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('181',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['120','138'])).

thf('182',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('183',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','183'])).

thf('185',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['110','184'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','188'])).

thf('190',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','53'])).

thf('194',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('199',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196','199'])).

thf('201',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('202',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('203',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['203'])).

thf('205',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','207'])).

thf('209',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','210'])).

thf('212',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('213',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196','199'])).

thf('214',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('215',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('216',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212','213','214','215'])).

thf('217',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('218',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','81','103'])).

thf('219',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('220',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217','220'])).

thf('222',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('223',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68','81','103'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('224',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('225',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('227',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('228',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('229',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('230',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['203'])).

thf('231',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['228','233'])).

thf('235',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('238',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('239',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['227','239'])).

thf('241',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('242',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196','199'])).

thf('245',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('246',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['226','246'])).

thf('248',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['225','247'])).

thf('249',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','248'])).

thf('250',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['203'])).

thf('252',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['250','251'])).

thf('253',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['221','252'])).

thf('254',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['192','253'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NNISplSDOu
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 350 iterations in 0.112s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.21/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(t169_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X6 : $i]:
% 0.21/0.57         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.21/0.57          | ~ (v1_relat_1 @ X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.57  thf(t62_tops_2, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.57                 ( m1_subset_1 @
% 0.21/0.57                   C @ 
% 0.21/0.57                   ( k1_zfmisc_1 @
% 0.21/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.57               ( ( ( ( k2_relset_1 @
% 0.21/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                   ( v2_funct_1 @ C ) ) =>
% 0.21/0.57                 ( ( ( k1_relset_1 @
% 0.21/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                       ( k2_tops_2 @
% 0.21/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                   ( ( k2_relset_1 @
% 0.21/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                       ( k2_tops_2 @
% 0.21/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( l1_struct_0 @ A ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.57              ( ![C:$i]:
% 0.21/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                    ( v1_funct_2 @
% 0.21/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.57                    ( m1_subset_1 @
% 0.21/0.57                      C @ 
% 0.21/0.57                      ( k1_zfmisc_1 @
% 0.21/0.57                        ( k2_zfmisc_1 @
% 0.21/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.57                  ( ( ( ( k2_relset_1 @
% 0.21/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                      ( v2_funct_1 @ C ) ) =>
% 0.21/0.57                    ( ( ( k1_relset_1 @
% 0.21/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                          ( k2_tops_2 @
% 0.21/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                      ( ( k2_relset_1 @
% 0.21/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                          ( k2_tops_2 @
% 0.21/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.21/0.57  thf('1', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t155_funct_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ( v2_funct_1 @ B ) =>
% 0.21/0.57         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X7)
% 0.21/0.57          | ((k10_relat_1 @ X7 @ X8) = (k9_relat_1 @ (k2_funct_1 @ X7) @ X8))
% 0.21/0.57          | ~ (v1_funct_1 @ X7)
% 0.21/0.57          | ~ (v1_relat_1 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ sk_C)
% 0.21/0.57          | ((k10_relat_1 @ sk_C @ X0)
% 0.21/0.57              = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.21/0.57          | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.57          | (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ 
% 0.21/0.57           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.21/0.57        | (v1_relat_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf(fc6_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('9', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k10_relat_1 @ sk_C @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.21/0.57  thf(t146_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X5 : $i]:
% 0.21/0.57         (((k9_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (k2_relat_1 @ X5))
% 0.21/0.57          | ~ (v1_relat_1 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.57          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.57        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf(d3_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['13', '18'])).
% 0.21/0.57  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.21/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.57  thf(cc5_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.57             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.57          | (v1_partfun1 @ X21 @ X22)
% 0.21/0.57          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.57          | ~ (v1_funct_1 @ X21)
% 0.21/0.57          | (v1_xboole_0 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '38', '45'])).
% 0.21/0.57  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf(fc5_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.57       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X27 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ (k2_struct_0 @ X27))
% 0.21/0.57          | ~ (l1_struct_0 @ X27)
% 0.21/0.57          | (v2_struct_0 @ X27))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.57  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('53', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('clc', [status(thm)], ['46', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup+', [status(thm)], ['28', '54'])).
% 0.21/0.57  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('57', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf(d4_partfun1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.57       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i]:
% 0.21/0.57         (~ (v1_partfun1 @ X25 @ X24)
% 0.21/0.57          | ((k1_relat_1 @ X25) = (X24))
% 0.21/0.57          | ~ (v4_relat_1 @ X25 @ X24)
% 0.21/0.57          | ~ (v1_relat_1 @ X25))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.57        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.21/0.57        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf(cc2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.57         ((v4_relat_1 @ X9 @ X10)
% 0.21/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('63', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.57  thf('64', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['27', '64'])).
% 0.21/0.57  thf(dt_k2_tops_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.21/0.57         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.21/0.57         ( m1_subset_1 @
% 0.21/0.57           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.21/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_tops_2 @ X31 @ X32 @ X33) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.21/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.57          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.57          | ~ (v1_funct_1 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | (m1_subset_1 @ 
% 0.21/0.57           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.21/0.57           (k1_zfmisc_1 @ 
% 0.21/0.57            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.57  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.57  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['69', '74'])).
% 0.21/0.57  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.57  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.57  thf('80', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['27', '64'])).
% 0.21/0.57  thf(d4_tops_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.57         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.21/0.57          | ~ (v2_funct_1 @ X30)
% 0.21/0.57          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.21/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.21/0.57          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.21/0.57          | ~ (v1_funct_1 @ X30))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.57        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57            != (k2_relat_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.57  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup+', [status(thm)], ['89', '90'])).
% 0.21/0.57  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.57  thf('94', plain,
% 0.21/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['88', '93'])).
% 0.21/0.57  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('97', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.21/0.57  thf('100', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57          = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['84', '85', '86', '87', '101'])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('simplify', [status(thm)], ['102'])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['67', '68', '81', '103'])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.57          | (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ 
% 0.21/0.57           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.21/0.57        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('108', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.57  thf('109', plain,
% 0.21/0.57      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.57         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['12', '108'])).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('111', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('112', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.57  thf('114', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_tops_2 @ X31 @ X32 @ X33) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.21/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.57          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.57          | ~ (v1_funct_1 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | (m1_subset_1 @ 
% 0.21/0.57           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.57           (k1_zfmisc_1 @ 
% 0.21/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.57  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('117', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.57  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['117', '118'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      ((m1_subset_1 @ 
% 0.21/0.57        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['115', '116', '119'])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.57  thf('123', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.21/0.57          | ~ (v2_funct_1 @ X30)
% 0.21/0.57          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.21/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.21/0.57          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.21/0.57          | ~ (v1_funct_1 @ X30))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.57        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            != (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.57  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('126', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['117', '118'])).
% 0.21/0.57  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('128', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('129', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.21/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['128', '129'])).
% 0.21/0.57  thf('131', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.21/0.57  thf('132', plain,
% 0.21/0.57      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['130', '131'])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['124', '125', '126', '127', '132'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.57        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['121', '133'])).
% 0.21/0.57  thf('135', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('137', plain,
% 0.21/0.57      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.57        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.21/0.57  thf('138', plain,
% 0.21/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('simplify', [status(thm)], ['137'])).
% 0.21/0.57  thf('139', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['120', '138'])).
% 0.21/0.57  thf('140', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.57          | (v1_partfun1 @ X21 @ X22)
% 0.21/0.57          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.57          | ~ (v1_funct_1 @ X21)
% 0.21/0.57          | (v1_xboole_0 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.57  thf('141', plain,
% 0.21/0.57      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.21/0.57        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.57        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.57             (k1_relat_1 @ sk_C))
% 0.21/0.57        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['139', '140'])).
% 0.21/0.57  thf('142', plain,
% 0.21/0.57      (![X26 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('143', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.57  thf('144', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k2_tops_2 @ X31 @ X32 @ X33))
% 0.21/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.57          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.57          | ~ (v1_funct_1 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.57  thf('145', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | (v1_funct_1 @ 
% 0.21/0.57           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['143', '144'])).
% 0.21/0.57  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('147', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['117', '118'])).
% 0.21/0.57  thf('148', plain,
% 0.21/0.57      ((v1_funct_1 @ 
% 0.21/0.57        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.21/0.57  thf('149', plain,
% 0.21/0.57      (((v1_funct_1 @ 
% 0.21/0.57         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['142', '148'])).
% 0.21/0.57  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('151', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('152', plain,
% 0.21/0.57      ((v1_funct_1 @ 
% 0.21/0.57        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.21/0.57  thf('153', plain,
% 0.21/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('simplify', [status(thm)], ['102'])).
% 0.21/0.57  thf('154', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['152', '153'])).
% 0.21/0.57  thf('155', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.57  thf('156', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((v1_funct_2 @ (k2_tops_2 @ X31 @ X32 @ X33) @ X32 @ X31)
% 0.21/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.57          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.57          | ~ (v1_funct_1 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.57  thf('157', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.40/0.57        | (v1_funct_2 @ 
% 0.40/0.57           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.57           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['155', '156'])).
% 0.40/0.57  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('159', plain,
% 0.40/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['117', '118'])).
% 0.40/0.57  thf('160', plain,
% 0.40/0.57      ((v1_funct_2 @ 
% 0.40/0.57        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.57        (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.40/0.57  thf('161', plain,
% 0.40/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.57         = (k2_funct_1 @ sk_C))),
% 0.40/0.57      inference('simplify', [status(thm)], ['137'])).
% 0.40/0.57  thf('162', plain,
% 0.40/0.57      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.57        (k1_relat_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['160', '161'])).
% 0.40/0.57  thf('163', plain,
% 0.40/0.57      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.40/0.57        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['141', '154', '162'])).
% 0.40/0.57  thf('164', plain,
% 0.40/0.57      (![X26 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('165', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(cc3_relset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.40/0.57       ( ![C:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57           ( v1_xboole_0 @ C ) ) ) ))).
% 0.40/0.57  thf('166', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (v1_xboole_0 @ X12)
% 0.40/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 0.40/0.57          | (v1_xboole_0 @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.40/0.57  thf('167', plain,
% 0.40/0.57      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['165', '166'])).
% 0.40/0.57  thf(fc11_relat_1, axiom,
% 0.40/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.40/0.57  thf('168', plain,
% 0.40/0.57      (![X2 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.40/0.57  thf('169', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.40/0.57      inference('clc', [status(thm)], ['51', '52'])).
% 0.40/0.57  thf('170', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.40/0.57      inference('sup-', [status(thm)], ['168', '169'])).
% 0.40/0.57  thf('171', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('clc', [status(thm)], ['167', '170'])).
% 0.40/0.57  thf('172', plain,
% 0.40/0.57      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['164', '171'])).
% 0.40/0.57  thf('173', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('174', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['172', '173'])).
% 0.40/0.57  thf('175', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.40/0.57  thf('176', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['174', '175'])).
% 0.40/0.57  thf('177', plain,
% 0.40/0.57      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.57      inference('clc', [status(thm)], ['163', '176'])).
% 0.40/0.57  thf('178', plain,
% 0.40/0.57      (![X24 : $i, X25 : $i]:
% 0.40/0.57         (~ (v1_partfun1 @ X25 @ X24)
% 0.40/0.57          | ((k1_relat_1 @ X25) = (X24))
% 0.40/0.57          | ~ (v4_relat_1 @ X25 @ X24)
% 0.40/0.57          | ~ (v1_relat_1 @ X25))),
% 0.40/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.57  thf('179', plain,
% 0.40/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.57        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.40/0.57        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['177', '178'])).
% 0.40/0.57  thf('180', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['106', '107'])).
% 0.40/0.57  thf('181', plain,
% 0.40/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.40/0.57      inference('demod', [status(thm)], ['120', '138'])).
% 0.40/0.57  thf('182', plain,
% 0.40/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.57         ((v4_relat_1 @ X9 @ X10)
% 0.40/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.57  thf('183', plain,
% 0.40/0.57      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.57      inference('sup-', [status(thm)], ['181', '182'])).
% 0.40/0.57  thf('184', plain,
% 0.40/0.57      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['179', '180', '183'])).
% 0.40/0.57  thf('185', plain,
% 0.40/0.57      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.57      inference('sup+', [status(thm)], ['110', '184'])).
% 0.40/0.57  thf('186', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.57  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('188', plain,
% 0.40/0.57      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.40/0.57  thf('189', plain,
% 0.40/0.57      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 0.40/0.57         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.57      inference('demod', [status(thm)], ['109', '188'])).
% 0.40/0.57  thf('190', plain,
% 0.40/0.57      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.57      inference('sup+', [status(thm)], ['0', '189'])).
% 0.40/0.57  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.57  thf('192', plain,
% 0.40/0.57      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.57      inference('demod', [status(thm)], ['190', '191'])).
% 0.40/0.57  thf('193', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('clc', [status(thm)], ['46', '53'])).
% 0.40/0.57  thf('194', plain,
% 0.40/0.57      (![X24 : $i, X25 : $i]:
% 0.40/0.57         (~ (v1_partfun1 @ X25 @ X24)
% 0.40/0.57          | ((k1_relat_1 @ X25) = (X24))
% 0.40/0.57          | ~ (v4_relat_1 @ X25 @ X24)
% 0.40/0.57          | ~ (v1_relat_1 @ X25))),
% 0.40/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.57  thf('195', plain,
% 0.40/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.57        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.40/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['193', '194'])).
% 0.40/0.57  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.57  thf('197', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('198', plain,
% 0.40/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.57         ((v4_relat_1 @ X9 @ X10)
% 0.40/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.57  thf('199', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['197', '198'])).
% 0.40/0.57  thf('200', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['195', '196', '199'])).
% 0.40/0.57  thf('201', plain,
% 0.40/0.57      (![X26 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('202', plain,
% 0.40/0.57      (![X26 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('203', plain,
% 0.40/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_B))
% 0.40/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57            != (k2_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('204', plain,
% 0.40/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_A)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('split', [status(esa)], ['203'])).
% 0.40/0.57  thf('205', plain,
% 0.40/0.57      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57           != (k2_struct_0 @ sk_A))
% 0.40/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['202', '204'])).
% 0.40/0.57  thf('206', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('207', plain,
% 0.40/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_A)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['205', '206'])).
% 0.40/0.57  thf('208', plain,
% 0.40/0.57      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57           != (k2_struct_0 @ sk_A))
% 0.40/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['201', '207'])).
% 0.40/0.57  thf('209', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('210', plain,
% 0.40/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_A)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['208', '209'])).
% 0.40/0.57  thf('211', plain,
% 0.40/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_A)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['200', '210'])).
% 0.40/0.57  thf('212', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.57  thf('213', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['195', '196', '199'])).
% 0.40/0.57  thf('214', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.57  thf('215', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.40/0.57  thf('216', plain,
% 0.40/0.57      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.57          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.40/0.57          != (k1_relat_1 @ sk_C)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['211', '212', '213', '214', '215'])).
% 0.40/0.57  thf('217', plain,
% 0.40/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.57         = (k2_funct_1 @ sk_C))),
% 0.40/0.57      inference('simplify', [status(thm)], ['102'])).
% 0.40/0.57  thf('218', plain,
% 0.40/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.40/0.57      inference('demod', [status(thm)], ['67', '68', '81', '103'])).
% 0.40/0.57  thf('219', plain,
% 0.40/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.57         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.40/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.57  thf('220', plain,
% 0.40/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.57         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['218', '219'])).
% 0.40/0.57  thf('221', plain,
% 0.40/0.57      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['216', '217', '220'])).
% 0.40/0.57  thf('222', plain,
% 0.40/0.57      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.40/0.57  thf('223', plain,
% 0.40/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.40/0.57      inference('demod', [status(thm)], ['67', '68', '81', '103'])).
% 0.40/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.57  thf('224', plain,
% 0.40/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.57         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.40/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.57  thf('225', plain,
% 0.40/0.57      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.57         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['223', '224'])).
% 0.40/0.57  thf('226', plain,
% 0.40/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.57         = (k2_funct_1 @ sk_C))),
% 0.40/0.57      inference('simplify', [status(thm)], ['102'])).
% 0.40/0.57  thf('227', plain,
% 0.40/0.57      (![X26 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('228', plain,
% 0.40/0.57      (![X26 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('229', plain,
% 0.40/0.57      (![X26 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('230', plain,
% 0.40/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_B))))),
% 0.40/0.57      inference('split', [status(esa)], ['203'])).
% 0.40/0.57  thf('231', plain,
% 0.40/0.57      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57           != (k2_struct_0 @ sk_B))
% 0.40/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_B))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['229', '230'])).
% 0.40/0.57  thf('232', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('233', plain,
% 0.40/0.57      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57          != (k2_struct_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.57                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['231', '232'])).
% 0.40/0.58  thf('234', plain,
% 0.40/0.58      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58           != (k2_struct_0 @ sk_B))
% 0.40/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['228', '233'])).
% 0.40/0.58  thf('235', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('236', plain,
% 0.40/0.58      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58          != (k2_struct_0 @ sk_B)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['234', '235'])).
% 0.40/0.58  thf('237', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.58  thf('238', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.58  thf('239', plain,
% 0.40/0.58      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58          != (k2_relat_1 @ sk_C)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['236', '237', '238'])).
% 0.40/0.58  thf('240', plain,
% 0.40/0.58      (((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58           != (k2_relat_1 @ sk_C))
% 0.40/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['227', '239'])).
% 0.40/0.58  thf('241', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.58  thf('242', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('243', plain,
% 0.40/0.58      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.40/0.58          != (k2_relat_1 @ sk_C)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['240', '241', '242'])).
% 0.40/0.58  thf('244', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['195', '196', '199'])).
% 0.40/0.58  thf('245', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.40/0.58  thf('246', plain,
% 0.40/0.58      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.58          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.40/0.58          != (k2_relat_1 @ sk_C)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['243', '244', '245'])).
% 0.40/0.58  thf('247', plain,
% 0.40/0.58      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.58          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['226', '246'])).
% 0.40/0.58  thf('248', plain,
% 0.40/0.58      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['225', '247'])).
% 0.40/0.58  thf('249', plain,
% 0.40/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.40/0.58         <= (~
% 0.40/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58                = (k2_struct_0 @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['222', '248'])).
% 0.40/0.58  thf('250', plain,
% 0.40/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58          = (k2_struct_0 @ sk_B)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['249'])).
% 0.40/0.58  thf('251', plain,
% 0.40/0.58      (~
% 0.40/0.58       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58          = (k2_struct_0 @ sk_A))) | 
% 0.40/0.58       ~
% 0.40/0.58       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58          = (k2_struct_0 @ sk_B)))),
% 0.40/0.58      inference('split', [status(esa)], ['203'])).
% 0.40/0.58  thf('252', plain,
% 0.40/0.58      (~
% 0.40/0.58       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.58          = (k2_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['250', '251'])).
% 0.40/0.58  thf('253', plain,
% 0.40/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['221', '252'])).
% 0.40/0.58  thf('254', plain, ($false),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['192', '253'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
