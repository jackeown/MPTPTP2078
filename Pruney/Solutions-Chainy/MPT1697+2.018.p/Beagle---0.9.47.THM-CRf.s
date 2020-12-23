%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:11 EST 2020

% Result     : Theorem 26.85s
% Output     : CNFRefutation 27.21s
% Verified   : 
% Statistics : Number of formulae       :  332 (3581 expanded)
%              Number of leaves         :   48 (1259 expanded)
%              Depth                    :   20
%              Number of atoms          :  910 (13674 expanded)
%              Number of equality atoms :  238 (2573 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v1_yellow_1,type,(
    v1_yellow_1: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_256,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_122,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v4_relat_1(B,A)
      & v1_funct_1(B)
      & v1_partfun1(B,A)
      & v1_yellow_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_214,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_180,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_48,plain,(
    ! [A_38] : v1_relat_1('#skF_1'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    ! [A_38] : v1_funct_1('#skF_1'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    ! [A_38] : v1_partfun1('#skF_1'(A_38),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    ! [A_38] : v4_relat_1('#skF_1'(A_38),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_89678,plain,(
    ! [A_3533] :
      ( k1_xboole_0 = A_3533
      | ~ v1_partfun1(A_3533,k1_xboole_0)
      | ~ v1_funct_1(A_3533)
      | ~ v4_relat_1(A_3533,k1_xboole_0)
      | ~ v1_relat_1(A_3533) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_89686,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_46,c_89678])).

tff(c_89693,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_89686])).

tff(c_87780,plain,(
    ! [B_3397,A_3398] :
      ( k1_relat_1(B_3397) = A_3398
      | ~ v1_partfun1(B_3397,A_3398)
      | ~ v4_relat_1(B_3397,A_3398)
      | ~ v1_relat_1(B_3397) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_87792,plain,(
    ! [A_38] :
      ( k1_relat_1('#skF_1'(A_38)) = A_38
      | ~ v1_partfun1('#skF_1'(A_38),A_38)
      | ~ v1_relat_1('#skF_1'(A_38)) ) ),
    inference(resolution,[status(thm)],[c_46,c_87780])).

tff(c_87804,plain,(
    ! [A_38] : k1_relat_1('#skF_1'(A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_87792])).

tff(c_89703,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89693,c_87804])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_78,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | ~ r1_subset_1(A_20,B_21)
      | v1_xboole_0(B_21)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_61142,plain,(
    ! [C_2597,A_2598,B_2599] :
      ( v1_relat_1(C_2597)
      | ~ m1_subset_1(C_2597,k1_zfmisc_1(k2_zfmisc_1(A_2598,B_2599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61154,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_61142])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_61156,plain,(
    ! [C_2600,A_2601,B_2602] :
      ( v4_relat_1(C_2600,A_2601)
      | ~ m1_subset_1(C_2600,k1_zfmisc_1(k2_zfmisc_1(A_2601,B_2602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_61168,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_61156])).

tff(c_87786,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_61168,c_87780])).

tff(c_87798,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_87786])).

tff(c_87835,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_87798])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_88777,plain,(
    ! [C_3478,A_3479,B_3480] :
      ( v1_partfun1(C_3478,A_3479)
      | ~ v1_funct_2(C_3478,A_3479,B_3480)
      | ~ v1_funct_1(C_3478)
      | ~ m1_subset_1(C_3478,k1_zfmisc_1(k2_zfmisc_1(A_3479,B_3480)))
      | v1_xboole_0(B_3480) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_88783,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_88777])).

tff(c_88794,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_88783])).

tff(c_88796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_87835,c_88794])).

tff(c_88797,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_87798])).

tff(c_14,plain,(
    ! [A_13,B_15] :
      ( k7_relat_1(A_13,B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,k1_relat_1(A_13))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88802,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_7',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88797,c_14])).

tff(c_89454,plain,(
    ! [B_3521] :
      ( k7_relat_1('#skF_7',B_3521) = k1_xboole_0
      | ~ r1_xboole_0(B_3521,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_88802])).

tff(c_89458,plain,(
    ! [A_20] :
      ( k7_relat_1('#skF_7',A_20) = k1_xboole_0
      | ~ r1_subset_1(A_20,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_89454])).

tff(c_89590,plain,(
    ! [A_3530] :
      ( k7_relat_1('#skF_7',A_3530) = k1_xboole_0
      | ~ r1_subset_1(A_3530,'#skF_5')
      | v1_xboole_0(A_3530) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_89458])).

tff(c_89593,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_89590])).

tff(c_89596,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_89593])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(k1_relat_1(B_19),A_18) = k1_relat_1(k7_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88805,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_18)) = k3_xboole_0('#skF_5',A_18)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88797,c_18])).

tff(c_88814,plain,(
    ! [A_18] : k1_relat_1(k7_relat_1('#skF_7',A_18)) = k3_xboole_0('#skF_5',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_88805])).

tff(c_89600,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_89596,c_88814])).

tff(c_89476,plain,(
    ! [B_3524,A_3525] :
      ( k7_relat_1(B_3524,k3_xboole_0(k1_relat_1(B_3524),A_3525)) = k7_relat_1(B_3524,A_3525)
      | ~ v1_relat_1(B_3524) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89510,plain,(
    ! [A_3525] :
      ( k7_relat_1('#skF_7',k3_xboole_0('#skF_5',A_3525)) = k7_relat_1('#skF_7',A_3525)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88797,c_89476])).

tff(c_89530,plain,(
    ! [A_3525] : k7_relat_1('#skF_7',k3_xboole_0('#skF_5',A_3525)) = k7_relat_1('#skF_7',A_3525) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_89510])).

tff(c_89607,plain,(
    k7_relat_1('#skF_7',k1_relat_1(k1_xboole_0)) = k7_relat_1('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_89600,c_89530])).

tff(c_89610,plain,(
    k7_relat_1('#skF_7',k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89596,c_89607])).

tff(c_89727,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89703,c_89610])).

tff(c_89728,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89703,c_89600])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87805,plain,(
    ! [A_3399] : k1_relat_1('#skF_1'(A_3399)) = A_3399 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_87792])).

tff(c_87811,plain,(
    ! [A_3399,B_15] :
      ( k7_relat_1('#skF_1'(A_3399),B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,A_3399)
      | ~ v1_relat_1('#skF_1'(A_3399)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87805,c_14])).

tff(c_87823,plain,(
    ! [A_3399,B_15] :
      ( k7_relat_1('#skF_1'(A_3399),B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,A_3399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_87811])).

tff(c_87814,plain,(
    ! [A_3399,A_18] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_3399),A_18)) = k3_xboole_0(A_3399,A_18)
      | ~ v1_relat_1('#skF_1'(A_3399)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87805,c_18])).

tff(c_89533,plain,(
    ! [A_3526,A_3527] : k1_relat_1(k7_relat_1('#skF_1'(A_3526),A_3527)) = k3_xboole_0(A_3526,A_3527) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_87814])).

tff(c_89558,plain,(
    ! [A_3399,B_15] :
      ( k3_xboole_0(A_3399,B_15) = k1_relat_1(k1_xboole_0)
      | ~ r1_xboole_0(B_15,A_3399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87823,c_89533])).

tff(c_89918,plain,(
    ! [A_3548,B_3549] :
      ( k3_xboole_0(A_3548,B_3549) = k1_xboole_0
      | ~ r1_xboole_0(B_3549,A_3548) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89703,c_89558])).

tff(c_89974,plain,(
    ! [B_3551,A_3552] :
      ( k3_xboole_0(B_3551,A_3552) = k1_xboole_0
      | k3_xboole_0(A_3552,B_3551) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_89918])).

tff(c_89984,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89728,c_89974])).

tff(c_89842,plain,(
    ! [A_3538,B_3539,C_3540,D_3541] :
      ( k2_partfun1(A_3538,B_3539,C_3540,D_3541) = k7_relat_1(C_3540,D_3541)
      | ~ m1_subset_1(C_3540,k1_zfmisc_1(k2_zfmisc_1(A_3538,B_3539)))
      | ~ v1_funct_1(C_3540) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_89846,plain,(
    ! [D_3541] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_3541) = k7_relat_1('#skF_7',D_3541)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_89842])).

tff(c_89855,plain,(
    ! [D_3541] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_3541) = k7_relat_1('#skF_7',D_3541) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_89846])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_61153,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_61142])).

tff(c_61167,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_61156])).

tff(c_87789,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_61167,c_87780])).

tff(c_87801,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61153,c_87789])).

tff(c_88828,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_87801])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_89361,plain,(
    ! [C_3515,A_3516,B_3517] :
      ( v1_partfun1(C_3515,A_3516)
      | ~ v1_funct_2(C_3515,A_3516,B_3517)
      | ~ v1_funct_1(C_3515)
      | ~ m1_subset_1(C_3515,k1_zfmisc_1(k2_zfmisc_1(A_3516,B_3517)))
      | v1_xboole_0(B_3517) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89364,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_89361])).

tff(c_89374,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_89364])).

tff(c_89376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_88828,c_89374])).

tff(c_89377,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_87801])).

tff(c_89507,plain,(
    ! [A_3525] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_3525)) = k7_relat_1('#skF_6',A_3525)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89377,c_89476])).

tff(c_89528,plain,(
    ! [A_3525] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_3525)) = k7_relat_1('#skF_6',A_3525) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61153,c_89507])).

tff(c_89844,plain,(
    ! [D_3541] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_3541) = k7_relat_1('#skF_6',D_3541)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_89842])).

tff(c_89852,plain,(
    ! [D_3541] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_3541) = k7_relat_1('#skF_6',D_3541) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89844])).

tff(c_87727,plain,(
    ! [A_3389,B_3390,C_3391] :
      ( k9_subset_1(A_3389,B_3390,C_3391) = k3_xboole_0(B_3390,C_3391)
      | ~ m1_subset_1(C_3391,k1_zfmisc_1(A_3389)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87740,plain,(
    ! [B_3390] : k9_subset_1('#skF_2',B_3390,'#skF_5') = k3_xboole_0(B_3390,'#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_87727])).

tff(c_4761,plain,(
    ! [A_653] :
      ( k1_xboole_0 = A_653
      | ~ v1_partfun1(A_653,k1_xboole_0)
      | ~ v1_funct_1(A_653)
      | ~ v4_relat_1(A_653,k1_xboole_0)
      | ~ v1_relat_1(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4769,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_46,c_4761])).

tff(c_4776,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_4769])).

tff(c_3032,plain,(
    ! [B_512,A_513] :
      ( k1_relat_1(B_512) = A_513
      | ~ v1_partfun1(B_512,A_513)
      | ~ v4_relat_1(B_512,A_513)
      | ~ v1_relat_1(B_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3044,plain,(
    ! [A_38] :
      ( k1_relat_1('#skF_1'(A_38)) = A_38
      | ~ v1_partfun1('#skF_1'(A_38),A_38)
      | ~ v1_relat_1('#skF_1'(A_38)) ) ),
    inference(resolution,[status(thm)],[c_46,c_3032])).

tff(c_3056,plain,(
    ! [A_38] : k1_relat_1('#skF_1'(A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_3044])).

tff(c_4786,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4776,c_3056])).

tff(c_2913,plain,(
    ! [C_481,A_482,B_483] :
      ( v1_relat_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2925,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_2913])).

tff(c_2927,plain,(
    ! [C_484,A_485,B_486] :
      ( v4_relat_1(C_484,A_485)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2939,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_2927])).

tff(c_3038,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2939,c_3032])).

tff(c_3050,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_3038])).

tff(c_3057,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3050])).

tff(c_3967,plain,(
    ! [C_592,A_593,B_594] :
      ( v1_partfun1(C_592,A_593)
      | ~ v1_funct_2(C_592,A_593,B_594)
      | ~ v1_funct_1(C_592)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594)))
      | v1_xboole_0(B_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3973,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3967])).

tff(c_3984,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3973])).

tff(c_3986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3057,c_3984])).

tff(c_3987,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3050])).

tff(c_3998,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_7',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3987,c_14])).

tff(c_4595,plain,(
    ! [B_635] :
      ( k7_relat_1('#skF_7',B_635) = k1_xboole_0
      | ~ r1_xboole_0(B_635,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_3998])).

tff(c_4599,plain,(
    ! [A_20] :
      ( k7_relat_1('#skF_7',A_20) = k1_xboole_0
      | ~ r1_subset_1(A_20,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_4595])).

tff(c_5066,plain,(
    ! [A_679] :
      ( k7_relat_1('#skF_7',A_679) = k1_xboole_0
      | ~ r1_subset_1(A_679,'#skF_5')
      | v1_xboole_0(A_679) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4599])).

tff(c_5069,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_5066])).

tff(c_5072,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5069])).

tff(c_4001,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_18)) = k3_xboole_0('#skF_5',A_18)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3987,c_18])).

tff(c_4011,plain,(
    ! [A_18] : k1_relat_1(k7_relat_1('#skF_7',A_18)) = k3_xboole_0('#skF_5',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_4001])).

tff(c_5076,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5072,c_4011])).

tff(c_5079,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4786,c_5076])).

tff(c_4532,plain,(
    ! [A_632] : k1_relat_1('#skF_1'(A_632)) = A_632 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_3044])).

tff(c_4544,plain,(
    ! [A_632,B_15] :
      ( k7_relat_1('#skF_1'(A_632),B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,A_632)
      | ~ v1_relat_1('#skF_1'(A_632)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4532,c_14])).

tff(c_4557,plain,(
    ! [A_632,B_15] :
      ( k7_relat_1('#skF_1'(A_632),B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,A_632) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4544])).

tff(c_4547,plain,(
    ! [A_632,A_18] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_632),A_18)) = k3_xboole_0(A_632,A_18)
      | ~ v1_relat_1('#skF_1'(A_632)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4532,c_18])).

tff(c_4695,plain,(
    ! [A_647,A_648] : k1_relat_1(k7_relat_1('#skF_1'(A_647),A_648)) = k3_xboole_0(A_647,A_648) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4547])).

tff(c_4716,plain,(
    ! [A_632,B_15] :
      ( k3_xboole_0(A_632,B_15) = k1_relat_1(k1_xboole_0)
      | ~ r1_xboole_0(B_15,A_632) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4557,c_4695])).

tff(c_4911,plain,(
    ! [A_663,B_664] :
      ( k3_xboole_0(A_663,B_664) = k1_xboole_0
      | ~ r1_xboole_0(B_664,A_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4786,c_4716])).

tff(c_4919,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(B_2,A_1) = k1_xboole_0
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_4911])).

tff(c_5092,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5079,c_4919])).

tff(c_4559,plain,(
    ! [A_632,A_18] : k1_relat_1(k7_relat_1('#skF_1'(A_632),A_18)) = k3_xboole_0(A_632,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4547])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,k3_xboole_0(k1_relat_1(B_17),A_16)) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4720,plain,(
    ! [A_647,A_16] :
      ( k3_xboole_0(A_647,k3_xboole_0(k1_relat_1('#skF_1'(A_647)),A_16)) = k1_relat_1(k7_relat_1('#skF_1'(A_647),A_16))
      | ~ v1_relat_1('#skF_1'(A_647)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4695])).

tff(c_4725,plain,(
    ! [A_647,A_16] : k3_xboole_0(A_647,k3_xboole_0(A_647,A_16)) = k3_xboole_0(A_647,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4559,c_3056,c_4720])).

tff(c_5101,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5092,c_4725])).

tff(c_5109,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5092,c_5101])).

tff(c_5164,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5109,c_4919])).

tff(c_2924,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_2913])).

tff(c_2938,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2927])).

tff(c_3041,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2938,c_3032])).

tff(c_3053,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2924,c_3041])).

tff(c_4014,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3053])).

tff(c_4461,plain,(
    ! [C_628,A_629,B_630] :
      ( v1_partfun1(C_628,A_629)
      | ~ v1_funct_2(C_628,A_629,B_630)
      | ~ v1_funct_1(C_628)
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k2_zfmisc_1(A_629,B_630)))
      | v1_xboole_0(B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4464,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4461])).

tff(c_4474,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4464])).

tff(c_4476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4014,c_4474])).

tff(c_4477,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3053])).

tff(c_4488,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_6',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4477,c_14])).

tff(c_4608,plain,(
    ! [B_636] :
      ( k7_relat_1('#skF_6',B_636) = k1_xboole_0
      | ~ r1_xboole_0(B_636,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2924,c_4488])).

tff(c_5386,plain,(
    ! [A_697] :
      ( k7_relat_1('#skF_6',A_697) = k1_xboole_0
      | k3_xboole_0(A_697,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_4608])).

tff(c_4482,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_16)) = k7_relat_1('#skF_6',A_16)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4477,c_16])).

tff(c_4495,plain,(
    ! [A_16] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_16)) = k7_relat_1('#skF_6',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2924,c_4482])).

tff(c_5104,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5092,c_4495])).

tff(c_5392,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5386,c_5104])).

tff(c_5418,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5164,c_5392])).

tff(c_5427,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5418,c_5104])).

tff(c_4880,plain,(
    ! [A_657,B_658,C_659,D_660] :
      ( k2_partfun1(A_657,B_658,C_659,D_660) = k7_relat_1(C_659,D_660)
      | ~ m1_subset_1(C_659,k1_zfmisc_1(k2_zfmisc_1(A_657,B_658)))
      | ~ v1_funct_1(C_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4882,plain,(
    ! [D_660] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_660) = k7_relat_1('#skF_6',D_660)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_4880])).

tff(c_4890,plain,(
    ! [D_660] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_660) = k7_relat_1('#skF_6',D_660) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4882])).

tff(c_3992,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_7',k3_xboole_0('#skF_5',A_16)) = k7_relat_1('#skF_7',A_16)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3987,c_16])).

tff(c_4005,plain,(
    ! [A_16] : k7_relat_1('#skF_7',k3_xboole_0('#skF_5',A_16)) = k7_relat_1('#skF_7',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_3992])).

tff(c_5089,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k7_relat_1('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5079,c_4005])).

tff(c_5094,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5072,c_5089])).

tff(c_4884,plain,(
    ! [D_660] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_660) = k7_relat_1('#skF_7',D_660)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_4880])).

tff(c_4893,plain,(
    ! [D_660] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_660) = k7_relat_1('#skF_7',D_660) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4884])).

tff(c_4621,plain,(
    ! [A_637,B_638,C_639] :
      ( k9_subset_1(A_637,B_638,C_639) = k3_xboole_0(B_638,C_639)
      | ~ m1_subset_1(C_639,k1_zfmisc_1(A_637)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4634,plain,(
    ! [B_638] : k9_subset_1('#skF_2',B_638,'#skF_5') = k3_xboole_0(B_638,'#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_4621])).

tff(c_64,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_97,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_4637,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_4634,c_97])).

tff(c_7024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5427,c_4890,c_5094,c_4893,c_5092,c_5092,c_4637])).

tff(c_7026,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) = k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_87743,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87740,c_87740,c_7026])).

tff(c_89860,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89852,c_87743])).

tff(c_89861,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89528,c_89860])).

tff(c_89887,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_89855,c_89861])).

tff(c_90053,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89727,c_89984,c_89887])).

tff(c_90016,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_89984,c_89528])).

tff(c_90094,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90053,c_90016])).

tff(c_90111,plain,(
    ! [F_3558,E_3556,A_3561,D_3559,B_3560,C_3557] :
      ( v1_funct_1(k1_tmap_1(A_3561,B_3560,C_3557,D_3559,E_3556,F_3558))
      | ~ m1_subset_1(F_3558,k1_zfmisc_1(k2_zfmisc_1(D_3559,B_3560)))
      | ~ v1_funct_2(F_3558,D_3559,B_3560)
      | ~ v1_funct_1(F_3558)
      | ~ m1_subset_1(E_3556,k1_zfmisc_1(k2_zfmisc_1(C_3557,B_3560)))
      | ~ v1_funct_2(E_3556,C_3557,B_3560)
      | ~ v1_funct_1(E_3556)
      | ~ m1_subset_1(D_3559,k1_zfmisc_1(A_3561))
      | v1_xboole_0(D_3559)
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3561))
      | v1_xboole_0(C_3557)
      | v1_xboole_0(B_3560)
      | v1_xboole_0(A_3561) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_90115,plain,(
    ! [A_3561,C_3557,E_3556] :
      ( v1_funct_1(k1_tmap_1(A_3561,'#skF_3',C_3557,'#skF_5',E_3556,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3556,k1_zfmisc_1(k2_zfmisc_1(C_3557,'#skF_3')))
      | ~ v1_funct_2(E_3556,C_3557,'#skF_3')
      | ~ v1_funct_1(E_3556)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3561))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3561))
      | v1_xboole_0(C_3557)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3561) ) ),
    inference(resolution,[status(thm)],[c_66,c_90111])).

tff(c_90125,plain,(
    ! [A_3561,C_3557,E_3556] :
      ( v1_funct_1(k1_tmap_1(A_3561,'#skF_3',C_3557,'#skF_5',E_3556,'#skF_7'))
      | ~ m1_subset_1(E_3556,k1_zfmisc_1(k2_zfmisc_1(C_3557,'#skF_3')))
      | ~ v1_funct_2(E_3556,C_3557,'#skF_3')
      | ~ v1_funct_1(E_3556)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3561))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3561))
      | v1_xboole_0(C_3557)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_90115])).

tff(c_90554,plain,(
    ! [A_3591,C_3592,E_3593] :
      ( v1_funct_1(k1_tmap_1(A_3591,'#skF_3',C_3592,'#skF_5',E_3593,'#skF_7'))
      | ~ m1_subset_1(E_3593,k1_zfmisc_1(k2_zfmisc_1(C_3592,'#skF_3')))
      | ~ v1_funct_2(E_3593,C_3592,'#skF_3')
      | ~ v1_funct_1(E_3593)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3591))
      | ~ m1_subset_1(C_3592,k1_zfmisc_1(A_3591))
      | v1_xboole_0(C_3592)
      | v1_xboole_0(A_3591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_90125])).

tff(c_90559,plain,(
    ! [A_3591] :
      ( v1_funct_1(k1_tmap_1(A_3591,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3591))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3591))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3591) ) ),
    inference(resolution,[status(thm)],[c_72,c_90554])).

tff(c_90570,plain,(
    ! [A_3591] :
      ( v1_funct_1(k1_tmap_1(A_3591,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3591))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3591))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_90559])).

tff(c_90795,plain,(
    ! [A_3612] :
      ( v1_funct_1(k1_tmap_1(A_3612,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3612))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3612))
      | v1_xboole_0(A_3612) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_90570])).

tff(c_90798,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_90795])).

tff(c_90801,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_90798])).

tff(c_90802,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_90801])).

tff(c_60,plain,(
    ! [F_173,C_170,D_171,A_168,B_169,E_172] :
      ( v1_funct_2(k1_tmap_1(A_168,B_169,C_170,D_171,E_172,F_173),k4_subset_1(A_168,C_170,D_171),B_169)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(D_171,B_169)))
      | ~ v1_funct_2(F_173,D_171,B_169)
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(C_170,B_169)))
      | ~ v1_funct_2(E_172,C_170,B_169)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(A_168))
      | v1_xboole_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | v1_xboole_0(C_170)
      | v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_58,plain,(
    ! [F_173,C_170,D_171,A_168,B_169,E_172] :
      ( m1_subset_1(k1_tmap_1(A_168,B_169,C_170,D_171,E_172,F_173),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_168,C_170,D_171),B_169)))
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(D_171,B_169)))
      | ~ v1_funct_2(F_173,D_171,B_169)
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(C_170,B_169)))
      | ~ v1_funct_2(E_172,C_170,B_169)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(A_168))
      | v1_xboole_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | v1_xboole_0(C_170)
      | v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_90638,plain,(
    ! [D_3595,E_3598,F_3599,C_3596,A_3594,B_3597] :
      ( k2_partfun1(k4_subset_1(A_3594,C_3596,D_3595),B_3597,k1_tmap_1(A_3594,B_3597,C_3596,D_3595,E_3598,F_3599),C_3596) = E_3598
      | ~ m1_subset_1(k1_tmap_1(A_3594,B_3597,C_3596,D_3595,E_3598,F_3599),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3594,C_3596,D_3595),B_3597)))
      | ~ v1_funct_2(k1_tmap_1(A_3594,B_3597,C_3596,D_3595,E_3598,F_3599),k4_subset_1(A_3594,C_3596,D_3595),B_3597)
      | ~ v1_funct_1(k1_tmap_1(A_3594,B_3597,C_3596,D_3595,E_3598,F_3599))
      | k2_partfun1(D_3595,B_3597,F_3599,k9_subset_1(A_3594,C_3596,D_3595)) != k2_partfun1(C_3596,B_3597,E_3598,k9_subset_1(A_3594,C_3596,D_3595))
      | ~ m1_subset_1(F_3599,k1_zfmisc_1(k2_zfmisc_1(D_3595,B_3597)))
      | ~ v1_funct_2(F_3599,D_3595,B_3597)
      | ~ v1_funct_1(F_3599)
      | ~ m1_subset_1(E_3598,k1_zfmisc_1(k2_zfmisc_1(C_3596,B_3597)))
      | ~ v1_funct_2(E_3598,C_3596,B_3597)
      | ~ v1_funct_1(E_3598)
      | ~ m1_subset_1(D_3595,k1_zfmisc_1(A_3594))
      | v1_xboole_0(D_3595)
      | ~ m1_subset_1(C_3596,k1_zfmisc_1(A_3594))
      | v1_xboole_0(C_3596)
      | v1_xboole_0(B_3597)
      | v1_xboole_0(A_3594) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_118479,plain,(
    ! [E_4279,A_4284,B_4283,C_4280,D_4282,F_4281] :
      ( k2_partfun1(k4_subset_1(A_4284,C_4280,D_4282),B_4283,k1_tmap_1(A_4284,B_4283,C_4280,D_4282,E_4279,F_4281),C_4280) = E_4279
      | ~ v1_funct_2(k1_tmap_1(A_4284,B_4283,C_4280,D_4282,E_4279,F_4281),k4_subset_1(A_4284,C_4280,D_4282),B_4283)
      | ~ v1_funct_1(k1_tmap_1(A_4284,B_4283,C_4280,D_4282,E_4279,F_4281))
      | k2_partfun1(D_4282,B_4283,F_4281,k9_subset_1(A_4284,C_4280,D_4282)) != k2_partfun1(C_4280,B_4283,E_4279,k9_subset_1(A_4284,C_4280,D_4282))
      | ~ m1_subset_1(F_4281,k1_zfmisc_1(k2_zfmisc_1(D_4282,B_4283)))
      | ~ v1_funct_2(F_4281,D_4282,B_4283)
      | ~ v1_funct_1(F_4281)
      | ~ m1_subset_1(E_4279,k1_zfmisc_1(k2_zfmisc_1(C_4280,B_4283)))
      | ~ v1_funct_2(E_4279,C_4280,B_4283)
      | ~ v1_funct_1(E_4279)
      | ~ m1_subset_1(D_4282,k1_zfmisc_1(A_4284))
      | v1_xboole_0(D_4282)
      | ~ m1_subset_1(C_4280,k1_zfmisc_1(A_4284))
      | v1_xboole_0(C_4280)
      | v1_xboole_0(B_4283)
      | v1_xboole_0(A_4284) ) ),
    inference(resolution,[status(thm)],[c_58,c_90638])).

tff(c_124029,plain,(
    ! [C_4464,F_4465,E_4463,A_4468,B_4467,D_4466] :
      ( k2_partfun1(k4_subset_1(A_4468,C_4464,D_4466),B_4467,k1_tmap_1(A_4468,B_4467,C_4464,D_4466,E_4463,F_4465),C_4464) = E_4463
      | ~ v1_funct_1(k1_tmap_1(A_4468,B_4467,C_4464,D_4466,E_4463,F_4465))
      | k2_partfun1(D_4466,B_4467,F_4465,k9_subset_1(A_4468,C_4464,D_4466)) != k2_partfun1(C_4464,B_4467,E_4463,k9_subset_1(A_4468,C_4464,D_4466))
      | ~ m1_subset_1(F_4465,k1_zfmisc_1(k2_zfmisc_1(D_4466,B_4467)))
      | ~ v1_funct_2(F_4465,D_4466,B_4467)
      | ~ v1_funct_1(F_4465)
      | ~ m1_subset_1(E_4463,k1_zfmisc_1(k2_zfmisc_1(C_4464,B_4467)))
      | ~ v1_funct_2(E_4463,C_4464,B_4467)
      | ~ v1_funct_1(E_4463)
      | ~ m1_subset_1(D_4466,k1_zfmisc_1(A_4468))
      | v1_xboole_0(D_4466)
      | ~ m1_subset_1(C_4464,k1_zfmisc_1(A_4468))
      | v1_xboole_0(C_4464)
      | v1_xboole_0(B_4467)
      | v1_xboole_0(A_4468) ) ),
    inference(resolution,[status(thm)],[c_60,c_118479])).

tff(c_124035,plain,(
    ! [A_4468,C_4464,E_4463] :
      ( k2_partfun1(k4_subset_1(A_4468,C_4464,'#skF_5'),'#skF_3',k1_tmap_1(A_4468,'#skF_3',C_4464,'#skF_5',E_4463,'#skF_7'),C_4464) = E_4463
      | ~ v1_funct_1(k1_tmap_1(A_4468,'#skF_3',C_4464,'#skF_5',E_4463,'#skF_7'))
      | k2_partfun1(C_4464,'#skF_3',E_4463,k9_subset_1(A_4468,C_4464,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_4468,C_4464,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_4463,k1_zfmisc_1(k2_zfmisc_1(C_4464,'#skF_3')))
      | ~ v1_funct_2(E_4463,C_4464,'#skF_3')
      | ~ v1_funct_1(E_4463)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4468))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4464,k1_zfmisc_1(A_4468))
      | v1_xboole_0(C_4464)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4468) ) ),
    inference(resolution,[status(thm)],[c_66,c_124029])).

tff(c_124046,plain,(
    ! [A_4468,C_4464,E_4463] :
      ( k2_partfun1(k4_subset_1(A_4468,C_4464,'#skF_5'),'#skF_3',k1_tmap_1(A_4468,'#skF_3',C_4464,'#skF_5',E_4463,'#skF_7'),C_4464) = E_4463
      | ~ v1_funct_1(k1_tmap_1(A_4468,'#skF_3',C_4464,'#skF_5',E_4463,'#skF_7'))
      | k2_partfun1(C_4464,'#skF_3',E_4463,k9_subset_1(A_4468,C_4464,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_4468,C_4464,'#skF_5'))
      | ~ m1_subset_1(E_4463,k1_zfmisc_1(k2_zfmisc_1(C_4464,'#skF_3')))
      | ~ v1_funct_2(E_4463,C_4464,'#skF_3')
      | ~ v1_funct_1(E_4463)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4468))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_4464,k1_zfmisc_1(A_4468))
      | v1_xboole_0(C_4464)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_89855,c_124035])).

tff(c_134190,plain,(
    ! [A_4595,C_4596,E_4597] :
      ( k2_partfun1(k4_subset_1(A_4595,C_4596,'#skF_5'),'#skF_3',k1_tmap_1(A_4595,'#skF_3',C_4596,'#skF_5',E_4597,'#skF_7'),C_4596) = E_4597
      | ~ v1_funct_1(k1_tmap_1(A_4595,'#skF_3',C_4596,'#skF_5',E_4597,'#skF_7'))
      | k2_partfun1(C_4596,'#skF_3',E_4597,k9_subset_1(A_4595,C_4596,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_4595,C_4596,'#skF_5'))
      | ~ m1_subset_1(E_4597,k1_zfmisc_1(k2_zfmisc_1(C_4596,'#skF_3')))
      | ~ v1_funct_2(E_4597,C_4596,'#skF_3')
      | ~ v1_funct_1(E_4597)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4595))
      | ~ m1_subset_1(C_4596,k1_zfmisc_1(A_4595))
      | v1_xboole_0(C_4596)
      | v1_xboole_0(A_4595) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_124046])).

tff(c_134195,plain,(
    ! [A_4595] :
      ( k2_partfun1(k4_subset_1(A_4595,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4595,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4595,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_4595,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_4595,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4595))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4595))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4595) ) ),
    inference(resolution,[status(thm)],[c_72,c_134190])).

tff(c_134206,plain,(
    ! [A_4595] :
      ( k2_partfun1(k4_subset_1(A_4595,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4595,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4595,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_4595,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_4595,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4595))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4595))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_4595) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_89852,c_134195])).

tff(c_135912,plain,(
    ! [A_4603] :
      ( k2_partfun1(k4_subset_1(A_4603,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_4603,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4603,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_4603,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_4603,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_4603))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4603))
      | v1_xboole_0(A_4603) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_134206])).

tff(c_63147,plain,(
    ! [A_2763] :
      ( k1_xboole_0 = A_2763
      | ~ v1_partfun1(A_2763,k1_xboole_0)
      | ~ v1_funct_1(A_2763)
      | ~ v4_relat_1(A_2763,k1_xboole_0)
      | ~ v1_relat_1(A_2763) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_63155,plain,
    ( '#skF_1'(k1_xboole_0) = k1_xboole_0
    | ~ v1_partfun1('#skF_1'(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1('#skF_1'(k1_xboole_0))
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_46,c_63147])).

tff(c_63162,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_63155])).

tff(c_61307,plain,(
    ! [B_2634,A_2635] :
      ( k1_relat_1(B_2634) = A_2635
      | ~ v1_partfun1(B_2634,A_2635)
      | ~ v4_relat_1(B_2634,A_2635)
      | ~ v1_relat_1(B_2634) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_61319,plain,(
    ! [A_38] :
      ( k1_relat_1('#skF_1'(A_38)) = A_38
      | ~ v1_partfun1('#skF_1'(A_38),A_38)
      | ~ v1_relat_1('#skF_1'(A_38)) ) ),
    inference(resolution,[status(thm)],[c_46,c_61307])).

tff(c_61331,plain,(
    ! [A_38] : k1_relat_1('#skF_1'(A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_61319])).

tff(c_63172,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63162,c_61331])).

tff(c_61313,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_61168,c_61307])).

tff(c_61325,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_61313])).

tff(c_61362,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_61325])).

tff(c_62240,plain,(
    ! [C_2711,A_2712,B_2713] :
      ( v1_partfun1(C_2711,A_2712)
      | ~ v1_funct_2(C_2711,A_2712,B_2713)
      | ~ v1_funct_1(C_2711)
      | ~ m1_subset_1(C_2711,k1_zfmisc_1(k2_zfmisc_1(A_2712,B_2713)))
      | v1_xboole_0(B_2713) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62246,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_62240])).

tff(c_62257,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62246])).

tff(c_62259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_61362,c_62257])).

tff(c_62260,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_61325])).

tff(c_62265,plain,(
    ! [B_15] :
      ( k7_relat_1('#skF_7',B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62260,c_14])).

tff(c_62904,plain,(
    ! [B_2750] :
      ( k7_relat_1('#skF_7',B_2750) = k1_xboole_0
      | ~ r1_xboole_0(B_2750,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_62265])).

tff(c_62908,plain,(
    ! [A_20] :
      ( k7_relat_1('#skF_7',A_20) = k1_xboole_0
      | ~ r1_subset_1(A_20,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_62904])).

tff(c_63059,plain,(
    ! [A_2760] :
      ( k7_relat_1('#skF_7',A_2760) = k1_xboole_0
      | ~ r1_subset_1(A_2760,'#skF_5')
      | v1_xboole_0(A_2760) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_62908])).

tff(c_63062,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_63059])).

tff(c_63065,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_63062])).

tff(c_62268,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_18)) = k3_xboole_0('#skF_5',A_18)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62260,c_18])).

tff(c_62277,plain,(
    ! [A_18] : k1_relat_1(k7_relat_1('#skF_7',A_18)) = k3_xboole_0('#skF_5',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_62268])).

tff(c_63069,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_63065,c_62277])).

tff(c_62955,plain,(
    ! [B_2754,A_2755] :
      ( k7_relat_1(B_2754,k3_xboole_0(k1_relat_1(B_2754),A_2755)) = k7_relat_1(B_2754,A_2755)
      | ~ v1_relat_1(B_2754) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62988,plain,(
    ! [A_2755] :
      ( k7_relat_1('#skF_7',k3_xboole_0('#skF_5',A_2755)) = k7_relat_1('#skF_7',A_2755)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62260,c_62955])).

tff(c_63006,plain,(
    ! [A_2755] : k7_relat_1('#skF_7',k3_xboole_0('#skF_5',A_2755)) = k7_relat_1('#skF_7',A_2755) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61154,c_62988])).

tff(c_63076,plain,(
    k7_relat_1('#skF_7',k1_relat_1(k1_xboole_0)) = k7_relat_1('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63069,c_63006])).

tff(c_63079,plain,(
    k7_relat_1('#skF_7',k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63065,c_63076])).

tff(c_63196,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63172,c_63079])).

tff(c_63197,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63172,c_63069])).

tff(c_61332,plain,(
    ! [A_2636] : k1_relat_1('#skF_1'(A_2636)) = A_2636 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_61319])).

tff(c_61338,plain,(
    ! [A_2636,B_15] :
      ( k7_relat_1('#skF_1'(A_2636),B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,A_2636)
      | ~ v1_relat_1('#skF_1'(A_2636)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61332,c_14])).

tff(c_63009,plain,(
    ! [A_2756,B_2757] :
      ( k7_relat_1('#skF_1'(A_2756),B_2757) = k1_xboole_0
      | ~ r1_xboole_0(B_2757,A_2756) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_61338])).

tff(c_61341,plain,(
    ! [A_2636,A_18] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_2636),A_18)) = k3_xboole_0(A_2636,A_18)
      | ~ v1_relat_1('#skF_1'(A_2636)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61332,c_18])).

tff(c_61352,plain,(
    ! [A_2636,A_18] : k1_relat_1(k7_relat_1('#skF_1'(A_2636),A_18)) = k3_xboole_0(A_2636,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_61341])).

tff(c_63019,plain,(
    ! [A_2756,B_2757] :
      ( k3_xboole_0(A_2756,B_2757) = k1_relat_1(k1_xboole_0)
      | ~ r1_xboole_0(B_2757,A_2756) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63009,c_61352])).

tff(c_63383,plain,(
    ! [A_2778,B_2779] :
      ( k3_xboole_0(A_2778,B_2779) = k1_xboole_0
      | ~ r1_xboole_0(B_2779,A_2778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63172,c_63019])).

tff(c_63393,plain,(
    ! [B_2780,A_2781] :
      ( k3_xboole_0(B_2780,A_2781) = k1_xboole_0
      | k3_xboole_0(A_2781,B_2780) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_63383])).

tff(c_63403,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63197,c_63393])).

tff(c_61316,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_61167,c_61307])).

tff(c_61328,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61153,c_61316])).

tff(c_62291,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61328])).

tff(c_62830,plain,(
    ! [C_2745,A_2746,B_2747] :
      ( v1_partfun1(C_2745,A_2746)
      | ~ v1_funct_2(C_2745,A_2746,B_2747)
      | ~ v1_funct_1(C_2745)
      | ~ m1_subset_1(C_2745,k1_zfmisc_1(k2_zfmisc_1(A_2746,B_2747)))
      | v1_xboole_0(B_2747) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62833,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_62830])).

tff(c_62843,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62833])).

tff(c_62845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_62291,c_62843])).

tff(c_62846,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_61328])).

tff(c_62985,plain,(
    ! [A_2755] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_2755)) = k7_relat_1('#skF_6',A_2755)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62846,c_62955])).

tff(c_63004,plain,(
    ! [A_2755] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_2755)) = k7_relat_1('#skF_6',A_2755) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61153,c_62985])).

tff(c_63308,plain,(
    ! [A_2768,B_2769,C_2770,D_2771] :
      ( k2_partfun1(A_2768,B_2769,C_2770,D_2771) = k7_relat_1(C_2770,D_2771)
      | ~ m1_subset_1(C_2770,k1_zfmisc_1(k2_zfmisc_1(A_2768,B_2769)))
      | ~ v1_funct_1(C_2770) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_63310,plain,(
    ! [D_2771] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_2771) = k7_relat_1('#skF_6',D_2771)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_63308])).

tff(c_63318,plain,(
    ! [D_2771] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_2771) = k7_relat_1('#skF_6',D_2771) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_63310])).

tff(c_61254,plain,(
    ! [A_2626,B_2627,C_2628] :
      ( k9_subset_1(A_2626,B_2627,C_2628) = k3_xboole_0(B_2627,C_2628)
      | ~ m1_subset_1(C_2628,k1_zfmisc_1(A_2626)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61267,plain,(
    ! [B_2627] : k9_subset_1('#skF_2',B_2627,'#skF_5') = k3_xboole_0(B_2627,'#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_61254])).

tff(c_61270,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61267,c_61267,c_7026])).

tff(c_63325,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63318,c_61270])).

tff(c_63326,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63004,c_63325])).

tff(c_63312,plain,(
    ! [D_2771] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_2771) = k7_relat_1('#skF_7',D_2771)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_63308])).

tff(c_63321,plain,(
    ! [D_2771] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_2771) = k7_relat_1('#skF_7',D_2771) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_63312])).

tff(c_63357,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) = k7_relat_1('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_63326,c_63321])).

tff(c_63488,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63196,c_63403,c_63357])).

tff(c_63413,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_63403,c_63004])).

tff(c_63512,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63488,c_63413])).

tff(c_63546,plain,(
    ! [E_2785,D_2788,C_2786,F_2787,A_2790,B_2789] :
      ( v1_funct_1(k1_tmap_1(A_2790,B_2789,C_2786,D_2788,E_2785,F_2787))
      | ~ m1_subset_1(F_2787,k1_zfmisc_1(k2_zfmisc_1(D_2788,B_2789)))
      | ~ v1_funct_2(F_2787,D_2788,B_2789)
      | ~ v1_funct_1(F_2787)
      | ~ m1_subset_1(E_2785,k1_zfmisc_1(k2_zfmisc_1(C_2786,B_2789)))
      | ~ v1_funct_2(E_2785,C_2786,B_2789)
      | ~ v1_funct_1(E_2785)
      | ~ m1_subset_1(D_2788,k1_zfmisc_1(A_2790))
      | v1_xboole_0(D_2788)
      | ~ m1_subset_1(C_2786,k1_zfmisc_1(A_2790))
      | v1_xboole_0(C_2786)
      | v1_xboole_0(B_2789)
      | v1_xboole_0(A_2790) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_63550,plain,(
    ! [A_2790,C_2786,E_2785] :
      ( v1_funct_1(k1_tmap_1(A_2790,'#skF_3',C_2786,'#skF_5',E_2785,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2785,k1_zfmisc_1(k2_zfmisc_1(C_2786,'#skF_3')))
      | ~ v1_funct_2(E_2785,C_2786,'#skF_3')
      | ~ v1_funct_1(E_2785)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2790))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2786,k1_zfmisc_1(A_2790))
      | v1_xboole_0(C_2786)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2790) ) ),
    inference(resolution,[status(thm)],[c_66,c_63546])).

tff(c_63560,plain,(
    ! [A_2790,C_2786,E_2785] :
      ( v1_funct_1(k1_tmap_1(A_2790,'#skF_3',C_2786,'#skF_5',E_2785,'#skF_7'))
      | ~ m1_subset_1(E_2785,k1_zfmisc_1(k2_zfmisc_1(C_2786,'#skF_3')))
      | ~ v1_funct_2(E_2785,C_2786,'#skF_3')
      | ~ v1_funct_1(E_2785)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2790))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2786,k1_zfmisc_1(A_2790))
      | v1_xboole_0(C_2786)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2790) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_63550])).

tff(c_64203,plain,(
    ! [A_2832,C_2833,E_2834] :
      ( v1_funct_1(k1_tmap_1(A_2832,'#skF_3',C_2833,'#skF_5',E_2834,'#skF_7'))
      | ~ m1_subset_1(E_2834,k1_zfmisc_1(k2_zfmisc_1(C_2833,'#skF_3')))
      | ~ v1_funct_2(E_2834,C_2833,'#skF_3')
      | ~ v1_funct_1(E_2834)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2832))
      | ~ m1_subset_1(C_2833,k1_zfmisc_1(A_2832))
      | v1_xboole_0(C_2833)
      | v1_xboole_0(A_2832) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_63560])).

tff(c_64208,plain,(
    ! [A_2832] :
      ( v1_funct_1(k1_tmap_1(A_2832,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2832))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2832))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2832) ) ),
    inference(resolution,[status(thm)],[c_72,c_64203])).

tff(c_64219,plain,(
    ! [A_2832] :
      ( v1_funct_1(k1_tmap_1(A_2832,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2832))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2832))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2832) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64208])).

tff(c_64719,plain,(
    ! [A_2853] :
      ( v1_funct_1(k1_tmap_1(A_2853,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2853))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2853))
      | v1_xboole_0(A_2853) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_64219])).

tff(c_64722,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_64719])).

tff(c_64725,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64722])).

tff(c_64726,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_64725])).

tff(c_64022,plain,(
    ! [E_2819,A_2815,F_2820,B_2818,C_2817,D_2816] :
      ( k2_partfun1(k4_subset_1(A_2815,C_2817,D_2816),B_2818,k1_tmap_1(A_2815,B_2818,C_2817,D_2816,E_2819,F_2820),D_2816) = F_2820
      | ~ m1_subset_1(k1_tmap_1(A_2815,B_2818,C_2817,D_2816,E_2819,F_2820),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2815,C_2817,D_2816),B_2818)))
      | ~ v1_funct_2(k1_tmap_1(A_2815,B_2818,C_2817,D_2816,E_2819,F_2820),k4_subset_1(A_2815,C_2817,D_2816),B_2818)
      | ~ v1_funct_1(k1_tmap_1(A_2815,B_2818,C_2817,D_2816,E_2819,F_2820))
      | k2_partfun1(D_2816,B_2818,F_2820,k9_subset_1(A_2815,C_2817,D_2816)) != k2_partfun1(C_2817,B_2818,E_2819,k9_subset_1(A_2815,C_2817,D_2816))
      | ~ m1_subset_1(F_2820,k1_zfmisc_1(k2_zfmisc_1(D_2816,B_2818)))
      | ~ v1_funct_2(F_2820,D_2816,B_2818)
      | ~ v1_funct_1(F_2820)
      | ~ m1_subset_1(E_2819,k1_zfmisc_1(k2_zfmisc_1(C_2817,B_2818)))
      | ~ v1_funct_2(E_2819,C_2817,B_2818)
      | ~ v1_funct_1(E_2819)
      | ~ m1_subset_1(D_2816,k1_zfmisc_1(A_2815))
      | v1_xboole_0(D_2816)
      | ~ m1_subset_1(C_2817,k1_zfmisc_1(A_2815))
      | v1_xboole_0(C_2817)
      | v1_xboole_0(B_2818)
      | v1_xboole_0(A_2815) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_68723,plain,(
    ! [D_3014,E_3011,F_3013,B_3015,C_3012,A_3016] :
      ( k2_partfun1(k4_subset_1(A_3016,C_3012,D_3014),B_3015,k1_tmap_1(A_3016,B_3015,C_3012,D_3014,E_3011,F_3013),D_3014) = F_3013
      | ~ v1_funct_2(k1_tmap_1(A_3016,B_3015,C_3012,D_3014,E_3011,F_3013),k4_subset_1(A_3016,C_3012,D_3014),B_3015)
      | ~ v1_funct_1(k1_tmap_1(A_3016,B_3015,C_3012,D_3014,E_3011,F_3013))
      | k2_partfun1(D_3014,B_3015,F_3013,k9_subset_1(A_3016,C_3012,D_3014)) != k2_partfun1(C_3012,B_3015,E_3011,k9_subset_1(A_3016,C_3012,D_3014))
      | ~ m1_subset_1(F_3013,k1_zfmisc_1(k2_zfmisc_1(D_3014,B_3015)))
      | ~ v1_funct_2(F_3013,D_3014,B_3015)
      | ~ v1_funct_1(F_3013)
      | ~ m1_subset_1(E_3011,k1_zfmisc_1(k2_zfmisc_1(C_3012,B_3015)))
      | ~ v1_funct_2(E_3011,C_3012,B_3015)
      | ~ v1_funct_1(E_3011)
      | ~ m1_subset_1(D_3014,k1_zfmisc_1(A_3016))
      | v1_xboole_0(D_3014)
      | ~ m1_subset_1(C_3012,k1_zfmisc_1(A_3016))
      | v1_xboole_0(C_3012)
      | v1_xboole_0(B_3015)
      | v1_xboole_0(A_3016) ) ),
    inference(resolution,[status(thm)],[c_58,c_64022])).

tff(c_75130,plain,(
    ! [B_3231,A_3232,C_3228,E_3227,D_3230,F_3229] :
      ( k2_partfun1(k4_subset_1(A_3232,C_3228,D_3230),B_3231,k1_tmap_1(A_3232,B_3231,C_3228,D_3230,E_3227,F_3229),D_3230) = F_3229
      | ~ v1_funct_1(k1_tmap_1(A_3232,B_3231,C_3228,D_3230,E_3227,F_3229))
      | k2_partfun1(D_3230,B_3231,F_3229,k9_subset_1(A_3232,C_3228,D_3230)) != k2_partfun1(C_3228,B_3231,E_3227,k9_subset_1(A_3232,C_3228,D_3230))
      | ~ m1_subset_1(F_3229,k1_zfmisc_1(k2_zfmisc_1(D_3230,B_3231)))
      | ~ v1_funct_2(F_3229,D_3230,B_3231)
      | ~ v1_funct_1(F_3229)
      | ~ m1_subset_1(E_3227,k1_zfmisc_1(k2_zfmisc_1(C_3228,B_3231)))
      | ~ v1_funct_2(E_3227,C_3228,B_3231)
      | ~ v1_funct_1(E_3227)
      | ~ m1_subset_1(D_3230,k1_zfmisc_1(A_3232))
      | v1_xboole_0(D_3230)
      | ~ m1_subset_1(C_3228,k1_zfmisc_1(A_3232))
      | v1_xboole_0(C_3228)
      | v1_xboole_0(B_3231)
      | v1_xboole_0(A_3232) ) ),
    inference(resolution,[status(thm)],[c_60,c_68723])).

tff(c_75136,plain,(
    ! [A_3232,C_3228,E_3227] :
      ( k2_partfun1(k4_subset_1(A_3232,C_3228,'#skF_5'),'#skF_3',k1_tmap_1(A_3232,'#skF_3',C_3228,'#skF_5',E_3227,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3232,'#skF_3',C_3228,'#skF_5',E_3227,'#skF_7'))
      | k2_partfun1(C_3228,'#skF_3',E_3227,k9_subset_1(A_3232,C_3228,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_3232,C_3228,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3227,k1_zfmisc_1(k2_zfmisc_1(C_3228,'#skF_3')))
      | ~ v1_funct_2(E_3227,C_3228,'#skF_3')
      | ~ v1_funct_1(E_3227)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3232))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3228,k1_zfmisc_1(A_3232))
      | v1_xboole_0(C_3228)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3232) ) ),
    inference(resolution,[status(thm)],[c_66,c_75130])).

tff(c_75147,plain,(
    ! [A_3232,C_3228,E_3227] :
      ( k2_partfun1(k4_subset_1(A_3232,C_3228,'#skF_5'),'#skF_3',k1_tmap_1(A_3232,'#skF_3',C_3228,'#skF_5',E_3227,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3232,'#skF_3',C_3228,'#skF_5',E_3227,'#skF_7'))
      | k2_partfun1(C_3228,'#skF_3',E_3227,k9_subset_1(A_3232,C_3228,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3232,C_3228,'#skF_5'))
      | ~ m1_subset_1(E_3227,k1_zfmisc_1(k2_zfmisc_1(C_3228,'#skF_3')))
      | ~ v1_funct_2(E_3227,C_3228,'#skF_3')
      | ~ v1_funct_1(E_3227)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3232))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3228,k1_zfmisc_1(A_3232))
      | v1_xboole_0(C_3228)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_63321,c_75136])).

tff(c_86548,plain,(
    ! [A_3379,C_3380,E_3381] :
      ( k2_partfun1(k4_subset_1(A_3379,C_3380,'#skF_5'),'#skF_3',k1_tmap_1(A_3379,'#skF_3',C_3380,'#skF_5',E_3381,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3379,'#skF_3',C_3380,'#skF_5',E_3381,'#skF_7'))
      | k2_partfun1(C_3380,'#skF_3',E_3381,k9_subset_1(A_3379,C_3380,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3379,C_3380,'#skF_5'))
      | ~ m1_subset_1(E_3381,k1_zfmisc_1(k2_zfmisc_1(C_3380,'#skF_3')))
      | ~ v1_funct_2(E_3381,C_3380,'#skF_3')
      | ~ v1_funct_1(E_3381)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3379))
      | ~ m1_subset_1(C_3380,k1_zfmisc_1(A_3379))
      | v1_xboole_0(C_3380)
      | v1_xboole_0(A_3379) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_75147])).

tff(c_86553,plain,(
    ! [A_3379] :
      ( k2_partfun1(k4_subset_1(A_3379,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3379,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3379,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_3379,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3379,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3379))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3379))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3379) ) ),
    inference(resolution,[status(thm)],[c_72,c_86548])).

tff(c_86564,plain,(
    ! [A_3379] :
      ( k2_partfun1(k4_subset_1(A_3379,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3379,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3379,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3379,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_3379,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3379))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3379))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_63318,c_86553])).

tff(c_87697,plain,(
    ! [A_3388] :
      ( k2_partfun1(k4_subset_1(A_3388,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3388,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3388,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3388,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_3388,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3388))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3388))
      | v1_xboole_0(A_3388) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_86564])).

tff(c_7025,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_61253,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7025])).

tff(c_87708,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87697,c_61253])).

tff(c_87722,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_63512,c_63403,c_61267,c_63196,c_63403,c_61267,c_64726,c_87708])).

tff(c_87724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_87722])).

tff(c_87725,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7025])).

tff(c_135924,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135912,c_87725])).

tff(c_135938,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_90094,c_89984,c_87740,c_89727,c_89984,c_87740,c_90802,c_135924])).

tff(c_135940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_135938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 18:11:35 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.85/17.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.85/17.95  
% 26.85/17.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.85/17.95  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_yellow_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 26.85/17.95  
% 26.85/17.95  %Foreground sorts:
% 26.85/17.95  
% 26.85/17.95  
% 26.85/17.95  %Background operators:
% 26.85/17.95  
% 26.85/17.95  
% 26.85/17.95  %Foreground operators:
% 26.85/17.95  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 26.85/17.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 26.85/17.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.85/17.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.85/17.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 26.85/17.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 26.85/17.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.85/17.95  tff('#skF_7', type, '#skF_7': $i).
% 26.85/17.95  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 26.85/17.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 26.85/17.95  tff('#skF_5', type, '#skF_5': $i).
% 26.85/17.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 26.85/17.95  tff('#skF_6', type, '#skF_6': $i).
% 26.85/17.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.85/17.95  tff('#skF_2', type, '#skF_2': $i).
% 26.85/17.95  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 26.85/17.95  tff('#skF_3', type, '#skF_3': $i).
% 26.85/17.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 26.85/17.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.85/17.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.85/17.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 26.85/17.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 26.85/17.95  tff('#skF_4', type, '#skF_4': $i).
% 26.85/17.95  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 26.85/17.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.85/17.95  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 26.85/17.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 26.85/17.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.85/17.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.85/17.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 26.85/17.95  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 26.85/17.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.85/17.95  
% 27.21/17.99  tff(f_256, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 27.21/17.99  tff(f_122, axiom, (![A]: (?[B]: ((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v1_yellow_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_1)).
% 27.21/17.99  tff(f_132, axiom, (![A]: ((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_pboole)).
% 27.21/17.99  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 27.21/17.99  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 27.21/17.99  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 27.21/17.99  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 27.21/17.99  tff(f_97, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 27.21/17.99  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 27.21/17.99  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 27.21/17.99  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 27.21/17.99  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 27.21/17.99  tff(f_111, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 27.21/17.99  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 27.21/17.99  tff(f_214, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 27.21/17.99  tff(f_180, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 27.21/17.99  tff(c_90, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_48, plain, (![A_38]: (v1_relat_1('#skF_1'(A_38)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.21/17.99  tff(c_44, plain, (![A_38]: (v1_funct_1('#skF_1'(A_38)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.21/17.99  tff(c_42, plain, (![A_38]: (v1_partfun1('#skF_1'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.21/17.99  tff(c_46, plain, (![A_38]: (v4_relat_1('#skF_1'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 27.21/17.99  tff(c_89678, plain, (![A_3533]: (k1_xboole_0=A_3533 | ~v1_partfun1(A_3533, k1_xboole_0) | ~v1_funct_1(A_3533) | ~v4_relat_1(A_3533, k1_xboole_0) | ~v1_relat_1(A_3533))), inference(cnfTransformation, [status(thm)], [f_132])).
% 27.21/17.99  tff(c_89686, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_89678])).
% 27.21/17.99  tff(c_89693, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_89686])).
% 27.21/17.99  tff(c_87780, plain, (![B_3397, A_3398]: (k1_relat_1(B_3397)=A_3398 | ~v1_partfun1(B_3397, A_3398) | ~v4_relat_1(B_3397, A_3398) | ~v1_relat_1(B_3397))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.21/17.99  tff(c_87792, plain, (![A_38]: (k1_relat_1('#skF_1'(A_38))=A_38 | ~v1_partfun1('#skF_1'(A_38), A_38) | ~v1_relat_1('#skF_1'(A_38)))), inference(resolution, [status(thm)], [c_46, c_87780])).
% 27.21/17.99  tff(c_87804, plain, (![A_38]: (k1_relat_1('#skF_1'(A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_87792])).
% 27.21/17.99  tff(c_89703, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89693, c_87804])).
% 27.21/17.99  tff(c_86, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_78, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_82, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | ~r1_subset_1(A_20, B_21) | v1_xboole_0(B_21) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 27.21/17.99  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_61142, plain, (![C_2597, A_2598, B_2599]: (v1_relat_1(C_2597) | ~m1_subset_1(C_2597, k1_zfmisc_1(k2_zfmisc_1(A_2598, B_2599))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.21/17.99  tff(c_61154, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_61142])).
% 27.21/17.99  tff(c_88, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_61156, plain, (![C_2600, A_2601, B_2602]: (v4_relat_1(C_2600, A_2601) | ~m1_subset_1(C_2600, k1_zfmisc_1(k2_zfmisc_1(A_2601, B_2602))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.21/17.99  tff(c_61168, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_61156])).
% 27.21/17.99  tff(c_87786, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_61168, c_87780])).
% 27.21/17.99  tff(c_87798, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_87786])).
% 27.21/17.99  tff(c_87835, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_87798])).
% 27.21/17.99  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_88777, plain, (![C_3478, A_3479, B_3480]: (v1_partfun1(C_3478, A_3479) | ~v1_funct_2(C_3478, A_3479, B_3480) | ~v1_funct_1(C_3478) | ~m1_subset_1(C_3478, k1_zfmisc_1(k2_zfmisc_1(A_3479, B_3480))) | v1_xboole_0(B_3480))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.21/17.99  tff(c_88783, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_88777])).
% 27.21/17.99  tff(c_88794, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_88783])).
% 27.21/17.99  tff(c_88796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_87835, c_88794])).
% 27.21/17.99  tff(c_88797, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_87798])).
% 27.21/17.99  tff(c_14, plain, (![A_13, B_15]: (k7_relat_1(A_13, B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, k1_relat_1(A_13)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.21/17.99  tff(c_88802, plain, (![B_15]: (k7_relat_1('#skF_7', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_88797, c_14])).
% 27.21/17.99  tff(c_89454, plain, (![B_3521]: (k7_relat_1('#skF_7', B_3521)=k1_xboole_0 | ~r1_xboole_0(B_3521, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_88802])).
% 27.21/17.99  tff(c_89458, plain, (![A_20]: (k7_relat_1('#skF_7', A_20)=k1_xboole_0 | ~r1_subset_1(A_20, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_22, c_89454])).
% 27.21/17.99  tff(c_89590, plain, (![A_3530]: (k7_relat_1('#skF_7', A_3530)=k1_xboole_0 | ~r1_subset_1(A_3530, '#skF_5') | v1_xboole_0(A_3530))), inference(negUnitSimplification, [status(thm)], [c_82, c_89458])).
% 27.21/17.99  tff(c_89593, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_89590])).
% 27.21/17.99  tff(c_89596, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_89593])).
% 27.21/17.99  tff(c_18, plain, (![B_19, A_18]: (k3_xboole_0(k1_relat_1(B_19), A_18)=k1_relat_1(k7_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 27.21/17.99  tff(c_88805, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_7', A_18))=k3_xboole_0('#skF_5', A_18) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_88797, c_18])).
% 27.21/17.99  tff(c_88814, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_7', A_18))=k3_xboole_0('#skF_5', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_88805])).
% 27.21/17.99  tff(c_89600, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89596, c_88814])).
% 27.21/17.99  tff(c_89476, plain, (![B_3524, A_3525]: (k7_relat_1(B_3524, k3_xboole_0(k1_relat_1(B_3524), A_3525))=k7_relat_1(B_3524, A_3525) | ~v1_relat_1(B_3524))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.21/17.99  tff(c_89510, plain, (![A_3525]: (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', A_3525))=k7_relat_1('#skF_7', A_3525) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_88797, c_89476])).
% 27.21/17.99  tff(c_89530, plain, (![A_3525]: (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', A_3525))=k7_relat_1('#skF_7', A_3525))), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_89510])).
% 27.21/17.99  tff(c_89607, plain, (k7_relat_1('#skF_7', k1_relat_1(k1_xboole_0))=k7_relat_1('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_89600, c_89530])).
% 27.21/17.99  tff(c_89610, plain, (k7_relat_1('#skF_7', k1_relat_1(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89596, c_89607])).
% 27.21/17.99  tff(c_89727, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89703, c_89610])).
% 27.21/17.99  tff(c_89728, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89703, c_89600])).
% 27.21/17.99  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.21/17.99  tff(c_87805, plain, (![A_3399]: (k1_relat_1('#skF_1'(A_3399))=A_3399)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_87792])).
% 27.21/17.99  tff(c_87811, plain, (![A_3399, B_15]: (k7_relat_1('#skF_1'(A_3399), B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, A_3399) | ~v1_relat_1('#skF_1'(A_3399)))), inference(superposition, [status(thm), theory('equality')], [c_87805, c_14])).
% 27.21/17.99  tff(c_87823, plain, (![A_3399, B_15]: (k7_relat_1('#skF_1'(A_3399), B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, A_3399))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_87811])).
% 27.21/17.99  tff(c_87814, plain, (![A_3399, A_18]: (k1_relat_1(k7_relat_1('#skF_1'(A_3399), A_18))=k3_xboole_0(A_3399, A_18) | ~v1_relat_1('#skF_1'(A_3399)))), inference(superposition, [status(thm), theory('equality')], [c_87805, c_18])).
% 27.21/17.99  tff(c_89533, plain, (![A_3526, A_3527]: (k1_relat_1(k7_relat_1('#skF_1'(A_3526), A_3527))=k3_xboole_0(A_3526, A_3527))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_87814])).
% 27.21/17.99  tff(c_89558, plain, (![A_3399, B_15]: (k3_xboole_0(A_3399, B_15)=k1_relat_1(k1_xboole_0) | ~r1_xboole_0(B_15, A_3399))), inference(superposition, [status(thm), theory('equality')], [c_87823, c_89533])).
% 27.21/17.99  tff(c_89918, plain, (![A_3548, B_3549]: (k3_xboole_0(A_3548, B_3549)=k1_xboole_0 | ~r1_xboole_0(B_3549, A_3548))), inference(demodulation, [status(thm), theory('equality')], [c_89703, c_89558])).
% 27.21/17.99  tff(c_89974, plain, (![B_3551, A_3552]: (k3_xboole_0(B_3551, A_3552)=k1_xboole_0 | k3_xboole_0(A_3552, B_3551)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_89918])).
% 27.21/17.99  tff(c_89984, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89728, c_89974])).
% 27.21/17.99  tff(c_89842, plain, (![A_3538, B_3539, C_3540, D_3541]: (k2_partfun1(A_3538, B_3539, C_3540, D_3541)=k7_relat_1(C_3540, D_3541) | ~m1_subset_1(C_3540, k1_zfmisc_1(k2_zfmisc_1(A_3538, B_3539))) | ~v1_funct_1(C_3540))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.21/17.99  tff(c_89846, plain, (![D_3541]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_3541)=k7_relat_1('#skF_7', D_3541) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_89842])).
% 27.21/17.99  tff(c_89855, plain, (![D_3541]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_3541)=k7_relat_1('#skF_7', D_3541))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_89846])).
% 27.21/17.99  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_61153, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_61142])).
% 27.21/17.99  tff(c_61167, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_61156])).
% 27.21/17.99  tff(c_87789, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_61167, c_87780])).
% 27.21/17.99  tff(c_87801, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61153, c_87789])).
% 27.21/17.99  tff(c_88828, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_87801])).
% 27.21/17.99  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_89361, plain, (![C_3515, A_3516, B_3517]: (v1_partfun1(C_3515, A_3516) | ~v1_funct_2(C_3515, A_3516, B_3517) | ~v1_funct_1(C_3515) | ~m1_subset_1(C_3515, k1_zfmisc_1(k2_zfmisc_1(A_3516, B_3517))) | v1_xboole_0(B_3517))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.21/17.99  tff(c_89364, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_89361])).
% 27.21/17.99  tff(c_89374, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_89364])).
% 27.21/17.99  tff(c_89376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_88828, c_89374])).
% 27.21/17.99  tff(c_89377, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_87801])).
% 27.21/17.99  tff(c_89507, plain, (![A_3525]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_3525))=k7_relat_1('#skF_6', A_3525) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_89377, c_89476])).
% 27.21/17.99  tff(c_89528, plain, (![A_3525]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_3525))=k7_relat_1('#skF_6', A_3525))), inference(demodulation, [status(thm), theory('equality')], [c_61153, c_89507])).
% 27.21/17.99  tff(c_89844, plain, (![D_3541]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_3541)=k7_relat_1('#skF_6', D_3541) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_89842])).
% 27.21/17.99  tff(c_89852, plain, (![D_3541]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_3541)=k7_relat_1('#skF_6', D_3541))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89844])).
% 27.21/17.99  tff(c_87727, plain, (![A_3389, B_3390, C_3391]: (k9_subset_1(A_3389, B_3390, C_3391)=k3_xboole_0(B_3390, C_3391) | ~m1_subset_1(C_3391, k1_zfmisc_1(A_3389)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.21/17.99  tff(c_87740, plain, (![B_3390]: (k9_subset_1('#skF_2', B_3390, '#skF_5')=k3_xboole_0(B_3390, '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_87727])).
% 27.21/17.99  tff(c_4761, plain, (![A_653]: (k1_xboole_0=A_653 | ~v1_partfun1(A_653, k1_xboole_0) | ~v1_funct_1(A_653) | ~v4_relat_1(A_653, k1_xboole_0) | ~v1_relat_1(A_653))), inference(cnfTransformation, [status(thm)], [f_132])).
% 27.21/17.99  tff(c_4769, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_4761])).
% 27.21/17.99  tff(c_4776, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_4769])).
% 27.21/17.99  tff(c_3032, plain, (![B_512, A_513]: (k1_relat_1(B_512)=A_513 | ~v1_partfun1(B_512, A_513) | ~v4_relat_1(B_512, A_513) | ~v1_relat_1(B_512))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.21/17.99  tff(c_3044, plain, (![A_38]: (k1_relat_1('#skF_1'(A_38))=A_38 | ~v1_partfun1('#skF_1'(A_38), A_38) | ~v1_relat_1('#skF_1'(A_38)))), inference(resolution, [status(thm)], [c_46, c_3032])).
% 27.21/17.99  tff(c_3056, plain, (![A_38]: (k1_relat_1('#skF_1'(A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_3044])).
% 27.21/17.99  tff(c_4786, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4776, c_3056])).
% 27.21/17.99  tff(c_2913, plain, (![C_481, A_482, B_483]: (v1_relat_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.21/17.99  tff(c_2925, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_2913])).
% 27.21/17.99  tff(c_2927, plain, (![C_484, A_485, B_486]: (v4_relat_1(C_484, A_485) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 27.21/17.99  tff(c_2939, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_2927])).
% 27.21/17.99  tff(c_3038, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2939, c_3032])).
% 27.21/17.99  tff(c_3050, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_3038])).
% 27.21/17.99  tff(c_3057, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_3050])).
% 27.21/17.99  tff(c_3967, plain, (![C_592, A_593, B_594]: (v1_partfun1(C_592, A_593) | ~v1_funct_2(C_592, A_593, B_594) | ~v1_funct_1(C_592) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))) | v1_xboole_0(B_594))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.21/17.99  tff(c_3973, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3967])).
% 27.21/17.99  tff(c_3984, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3973])).
% 27.21/17.99  tff(c_3986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3057, c_3984])).
% 27.21/17.99  tff(c_3987, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_3050])).
% 27.21/17.99  tff(c_3998, plain, (![B_15]: (k7_relat_1('#skF_7', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3987, c_14])).
% 27.21/17.99  tff(c_4595, plain, (![B_635]: (k7_relat_1('#skF_7', B_635)=k1_xboole_0 | ~r1_xboole_0(B_635, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_3998])).
% 27.21/17.99  tff(c_4599, plain, (![A_20]: (k7_relat_1('#skF_7', A_20)=k1_xboole_0 | ~r1_subset_1(A_20, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_22, c_4595])).
% 27.21/17.99  tff(c_5066, plain, (![A_679]: (k7_relat_1('#skF_7', A_679)=k1_xboole_0 | ~r1_subset_1(A_679, '#skF_5') | v1_xboole_0(A_679))), inference(negUnitSimplification, [status(thm)], [c_82, c_4599])).
% 27.21/17.99  tff(c_5069, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_5066])).
% 27.21/17.99  tff(c_5072, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_5069])).
% 27.21/17.99  tff(c_4001, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_7', A_18))=k3_xboole_0('#skF_5', A_18) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3987, c_18])).
% 27.21/17.99  tff(c_4011, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_7', A_18))=k3_xboole_0('#skF_5', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_4001])).
% 27.21/17.99  tff(c_5076, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5072, c_4011])).
% 27.21/17.99  tff(c_5079, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4786, c_5076])).
% 27.21/17.99  tff(c_4532, plain, (![A_632]: (k1_relat_1('#skF_1'(A_632))=A_632)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_3044])).
% 27.21/17.99  tff(c_4544, plain, (![A_632, B_15]: (k7_relat_1('#skF_1'(A_632), B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, A_632) | ~v1_relat_1('#skF_1'(A_632)))), inference(superposition, [status(thm), theory('equality')], [c_4532, c_14])).
% 27.21/17.99  tff(c_4557, plain, (![A_632, B_15]: (k7_relat_1('#skF_1'(A_632), B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, A_632))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4544])).
% 27.21/17.99  tff(c_4547, plain, (![A_632, A_18]: (k1_relat_1(k7_relat_1('#skF_1'(A_632), A_18))=k3_xboole_0(A_632, A_18) | ~v1_relat_1('#skF_1'(A_632)))), inference(superposition, [status(thm), theory('equality')], [c_4532, c_18])).
% 27.21/17.99  tff(c_4695, plain, (![A_647, A_648]: (k1_relat_1(k7_relat_1('#skF_1'(A_647), A_648))=k3_xboole_0(A_647, A_648))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4547])).
% 27.21/17.99  tff(c_4716, plain, (![A_632, B_15]: (k3_xboole_0(A_632, B_15)=k1_relat_1(k1_xboole_0) | ~r1_xboole_0(B_15, A_632))), inference(superposition, [status(thm), theory('equality')], [c_4557, c_4695])).
% 27.21/17.99  tff(c_4911, plain, (![A_663, B_664]: (k3_xboole_0(A_663, B_664)=k1_xboole_0 | ~r1_xboole_0(B_664, A_663))), inference(demodulation, [status(thm), theory('equality')], [c_4786, c_4716])).
% 27.21/17.99  tff(c_4919, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k1_xboole_0 | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_4911])).
% 27.21/17.99  tff(c_5092, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5079, c_4919])).
% 27.21/17.99  tff(c_4559, plain, (![A_632, A_18]: (k1_relat_1(k7_relat_1('#skF_1'(A_632), A_18))=k3_xboole_0(A_632, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4547])).
% 27.21/17.99  tff(c_16, plain, (![B_17, A_16]: (k7_relat_1(B_17, k3_xboole_0(k1_relat_1(B_17), A_16))=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.21/17.99  tff(c_4720, plain, (![A_647, A_16]: (k3_xboole_0(A_647, k3_xboole_0(k1_relat_1('#skF_1'(A_647)), A_16))=k1_relat_1(k7_relat_1('#skF_1'(A_647), A_16)) | ~v1_relat_1('#skF_1'(A_647)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4695])).
% 27.21/17.99  tff(c_4725, plain, (![A_647, A_16]: (k3_xboole_0(A_647, k3_xboole_0(A_647, A_16))=k3_xboole_0(A_647, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4559, c_3056, c_4720])).
% 27.21/17.99  tff(c_5101, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5092, c_4725])).
% 27.21/17.99  tff(c_5109, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5092, c_5101])).
% 27.21/17.99  tff(c_5164, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5109, c_4919])).
% 27.21/17.99  tff(c_2924, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_2913])).
% 27.21/17.99  tff(c_2938, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_2927])).
% 27.21/17.99  tff(c_3041, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2938, c_3032])).
% 27.21/17.99  tff(c_3053, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2924, c_3041])).
% 27.21/17.99  tff(c_4014, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_3053])).
% 27.21/17.99  tff(c_4461, plain, (![C_628, A_629, B_630]: (v1_partfun1(C_628, A_629) | ~v1_funct_2(C_628, A_629, B_630) | ~v1_funct_1(C_628) | ~m1_subset_1(C_628, k1_zfmisc_1(k2_zfmisc_1(A_629, B_630))) | v1_xboole_0(B_630))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.21/17.99  tff(c_4464, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_4461])).
% 27.21/17.99  tff(c_4474, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4464])).
% 27.21/17.99  tff(c_4476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_4014, c_4474])).
% 27.21/17.99  tff(c_4477, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_3053])).
% 27.21/17.99  tff(c_4488, plain, (![B_15]: (k7_relat_1('#skF_6', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4477, c_14])).
% 27.21/17.99  tff(c_4608, plain, (![B_636]: (k7_relat_1('#skF_6', B_636)=k1_xboole_0 | ~r1_xboole_0(B_636, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2924, c_4488])).
% 27.21/17.99  tff(c_5386, plain, (![A_697]: (k7_relat_1('#skF_6', A_697)=k1_xboole_0 | k3_xboole_0(A_697, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_4608])).
% 27.21/17.99  tff(c_4482, plain, (![A_16]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_16))=k7_relat_1('#skF_6', A_16) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4477, c_16])).
% 27.21/17.99  tff(c_4495, plain, (![A_16]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_16))=k7_relat_1('#skF_6', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2924, c_4482])).
% 27.21/17.99  tff(c_5104, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5092, c_4495])).
% 27.21/17.99  tff(c_5392, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5386, c_5104])).
% 27.21/17.99  tff(c_5418, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5164, c_5392])).
% 27.21/17.99  tff(c_5427, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5418, c_5104])).
% 27.21/17.99  tff(c_4880, plain, (![A_657, B_658, C_659, D_660]: (k2_partfun1(A_657, B_658, C_659, D_660)=k7_relat_1(C_659, D_660) | ~m1_subset_1(C_659, k1_zfmisc_1(k2_zfmisc_1(A_657, B_658))) | ~v1_funct_1(C_659))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.21/17.99  tff(c_4882, plain, (![D_660]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_660)=k7_relat_1('#skF_6', D_660) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_4880])).
% 27.21/17.99  tff(c_4890, plain, (![D_660]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_660)=k7_relat_1('#skF_6', D_660))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4882])).
% 27.21/17.99  tff(c_3992, plain, (![A_16]: (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', A_16))=k7_relat_1('#skF_7', A_16) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3987, c_16])).
% 27.21/17.99  tff(c_4005, plain, (![A_16]: (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', A_16))=k7_relat_1('#skF_7', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_3992])).
% 27.21/17.99  tff(c_5089, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k7_relat_1('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5079, c_4005])).
% 27.21/17.99  tff(c_5094, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5072, c_5089])).
% 27.21/17.99  tff(c_4884, plain, (![D_660]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_660)=k7_relat_1('#skF_7', D_660) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_4880])).
% 27.21/17.99  tff(c_4893, plain, (![D_660]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_660)=k7_relat_1('#skF_7', D_660))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4884])).
% 27.21/17.99  tff(c_4621, plain, (![A_637, B_638, C_639]: (k9_subset_1(A_637, B_638, C_639)=k3_xboole_0(B_638, C_639) | ~m1_subset_1(C_639, k1_zfmisc_1(A_637)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.21/17.99  tff(c_4634, plain, (![B_638]: (k9_subset_1('#skF_2', B_638, '#skF_5')=k3_xboole_0(B_638, '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_4621])).
% 27.21/17.99  tff(c_64, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 27.21/17.99  tff(c_97, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_64])).
% 27.21/17.99  tff(c_4637, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4634, c_4634, c_97])).
% 27.21/17.99  tff(c_7024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5427, c_4890, c_5094, c_4893, c_5092, c_5092, c_4637])).
% 27.21/17.99  tff(c_7026, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_64])).
% 27.21/17.99  tff(c_87743, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_87740, c_87740, c_7026])).
% 27.21/17.99  tff(c_89860, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_89852, c_87743])).
% 27.21/17.99  tff(c_89861, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89528, c_89860])).
% 27.21/17.99  tff(c_89887, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_89855, c_89861])).
% 27.21/17.99  tff(c_90053, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89727, c_89984, c_89887])).
% 27.21/17.99  tff(c_90016, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_89984, c_89528])).
% 27.21/17.99  tff(c_90094, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_90053, c_90016])).
% 27.21/17.99  tff(c_90111, plain, (![F_3558, E_3556, A_3561, D_3559, B_3560, C_3557]: (v1_funct_1(k1_tmap_1(A_3561, B_3560, C_3557, D_3559, E_3556, F_3558)) | ~m1_subset_1(F_3558, k1_zfmisc_1(k2_zfmisc_1(D_3559, B_3560))) | ~v1_funct_2(F_3558, D_3559, B_3560) | ~v1_funct_1(F_3558) | ~m1_subset_1(E_3556, k1_zfmisc_1(k2_zfmisc_1(C_3557, B_3560))) | ~v1_funct_2(E_3556, C_3557, B_3560) | ~v1_funct_1(E_3556) | ~m1_subset_1(D_3559, k1_zfmisc_1(A_3561)) | v1_xboole_0(D_3559) | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3561)) | v1_xboole_0(C_3557) | v1_xboole_0(B_3560) | v1_xboole_0(A_3561))), inference(cnfTransformation, [status(thm)], [f_214])).
% 27.21/17.99  tff(c_90115, plain, (![A_3561, C_3557, E_3556]: (v1_funct_1(k1_tmap_1(A_3561, '#skF_3', C_3557, '#skF_5', E_3556, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3556, k1_zfmisc_1(k2_zfmisc_1(C_3557, '#skF_3'))) | ~v1_funct_2(E_3556, C_3557, '#skF_3') | ~v1_funct_1(E_3556) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3561)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3561)) | v1_xboole_0(C_3557) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3561))), inference(resolution, [status(thm)], [c_66, c_90111])).
% 27.21/17.99  tff(c_90125, plain, (![A_3561, C_3557, E_3556]: (v1_funct_1(k1_tmap_1(A_3561, '#skF_3', C_3557, '#skF_5', E_3556, '#skF_7')) | ~m1_subset_1(E_3556, k1_zfmisc_1(k2_zfmisc_1(C_3557, '#skF_3'))) | ~v1_funct_2(E_3556, C_3557, '#skF_3') | ~v1_funct_1(E_3556) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3561)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3561)) | v1_xboole_0(C_3557) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3561))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_90115])).
% 27.21/17.99  tff(c_90554, plain, (![A_3591, C_3592, E_3593]: (v1_funct_1(k1_tmap_1(A_3591, '#skF_3', C_3592, '#skF_5', E_3593, '#skF_7')) | ~m1_subset_1(E_3593, k1_zfmisc_1(k2_zfmisc_1(C_3592, '#skF_3'))) | ~v1_funct_2(E_3593, C_3592, '#skF_3') | ~v1_funct_1(E_3593) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3591)) | ~m1_subset_1(C_3592, k1_zfmisc_1(A_3591)) | v1_xboole_0(C_3592) | v1_xboole_0(A_3591))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_90125])).
% 27.21/17.99  tff(c_90559, plain, (![A_3591]: (v1_funct_1(k1_tmap_1(A_3591, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3591)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3591)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3591))), inference(resolution, [status(thm)], [c_72, c_90554])).
% 27.21/17.99  tff(c_90570, plain, (![A_3591]: (v1_funct_1(k1_tmap_1(A_3591, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3591)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3591)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3591))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_90559])).
% 27.21/17.99  tff(c_90795, plain, (![A_3612]: (v1_funct_1(k1_tmap_1(A_3612, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3612)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3612)) | v1_xboole_0(A_3612))), inference(negUnitSimplification, [status(thm)], [c_86, c_90570])).
% 27.21/17.99  tff(c_90798, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_90795])).
% 27.21/17.99  tff(c_90801, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_90798])).
% 27.21/17.99  tff(c_90802, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_90, c_90801])).
% 27.21/17.99  tff(c_60, plain, (![F_173, C_170, D_171, A_168, B_169, E_172]: (v1_funct_2(k1_tmap_1(A_168, B_169, C_170, D_171, E_172, F_173), k4_subset_1(A_168, C_170, D_171), B_169) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(D_171, B_169))) | ~v1_funct_2(F_173, D_171, B_169) | ~v1_funct_1(F_173) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(C_170, B_169))) | ~v1_funct_2(E_172, C_170, B_169) | ~v1_funct_1(E_172) | ~m1_subset_1(D_171, k1_zfmisc_1(A_168)) | v1_xboole_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | v1_xboole_0(C_170) | v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_214])).
% 27.21/17.99  tff(c_58, plain, (![F_173, C_170, D_171, A_168, B_169, E_172]: (m1_subset_1(k1_tmap_1(A_168, B_169, C_170, D_171, E_172, F_173), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_168, C_170, D_171), B_169))) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(D_171, B_169))) | ~v1_funct_2(F_173, D_171, B_169) | ~v1_funct_1(F_173) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(C_170, B_169))) | ~v1_funct_2(E_172, C_170, B_169) | ~v1_funct_1(E_172) | ~m1_subset_1(D_171, k1_zfmisc_1(A_168)) | v1_xboole_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | v1_xboole_0(C_170) | v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_214])).
% 27.21/17.99  tff(c_90638, plain, (![D_3595, E_3598, F_3599, C_3596, A_3594, B_3597]: (k2_partfun1(k4_subset_1(A_3594, C_3596, D_3595), B_3597, k1_tmap_1(A_3594, B_3597, C_3596, D_3595, E_3598, F_3599), C_3596)=E_3598 | ~m1_subset_1(k1_tmap_1(A_3594, B_3597, C_3596, D_3595, E_3598, F_3599), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3594, C_3596, D_3595), B_3597))) | ~v1_funct_2(k1_tmap_1(A_3594, B_3597, C_3596, D_3595, E_3598, F_3599), k4_subset_1(A_3594, C_3596, D_3595), B_3597) | ~v1_funct_1(k1_tmap_1(A_3594, B_3597, C_3596, D_3595, E_3598, F_3599)) | k2_partfun1(D_3595, B_3597, F_3599, k9_subset_1(A_3594, C_3596, D_3595))!=k2_partfun1(C_3596, B_3597, E_3598, k9_subset_1(A_3594, C_3596, D_3595)) | ~m1_subset_1(F_3599, k1_zfmisc_1(k2_zfmisc_1(D_3595, B_3597))) | ~v1_funct_2(F_3599, D_3595, B_3597) | ~v1_funct_1(F_3599) | ~m1_subset_1(E_3598, k1_zfmisc_1(k2_zfmisc_1(C_3596, B_3597))) | ~v1_funct_2(E_3598, C_3596, B_3597) | ~v1_funct_1(E_3598) | ~m1_subset_1(D_3595, k1_zfmisc_1(A_3594)) | v1_xboole_0(D_3595) | ~m1_subset_1(C_3596, k1_zfmisc_1(A_3594)) | v1_xboole_0(C_3596) | v1_xboole_0(B_3597) | v1_xboole_0(A_3594))), inference(cnfTransformation, [status(thm)], [f_180])).
% 27.21/17.99  tff(c_118479, plain, (![E_4279, A_4284, B_4283, C_4280, D_4282, F_4281]: (k2_partfun1(k4_subset_1(A_4284, C_4280, D_4282), B_4283, k1_tmap_1(A_4284, B_4283, C_4280, D_4282, E_4279, F_4281), C_4280)=E_4279 | ~v1_funct_2(k1_tmap_1(A_4284, B_4283, C_4280, D_4282, E_4279, F_4281), k4_subset_1(A_4284, C_4280, D_4282), B_4283) | ~v1_funct_1(k1_tmap_1(A_4284, B_4283, C_4280, D_4282, E_4279, F_4281)) | k2_partfun1(D_4282, B_4283, F_4281, k9_subset_1(A_4284, C_4280, D_4282))!=k2_partfun1(C_4280, B_4283, E_4279, k9_subset_1(A_4284, C_4280, D_4282)) | ~m1_subset_1(F_4281, k1_zfmisc_1(k2_zfmisc_1(D_4282, B_4283))) | ~v1_funct_2(F_4281, D_4282, B_4283) | ~v1_funct_1(F_4281) | ~m1_subset_1(E_4279, k1_zfmisc_1(k2_zfmisc_1(C_4280, B_4283))) | ~v1_funct_2(E_4279, C_4280, B_4283) | ~v1_funct_1(E_4279) | ~m1_subset_1(D_4282, k1_zfmisc_1(A_4284)) | v1_xboole_0(D_4282) | ~m1_subset_1(C_4280, k1_zfmisc_1(A_4284)) | v1_xboole_0(C_4280) | v1_xboole_0(B_4283) | v1_xboole_0(A_4284))), inference(resolution, [status(thm)], [c_58, c_90638])).
% 27.21/17.99  tff(c_124029, plain, (![C_4464, F_4465, E_4463, A_4468, B_4467, D_4466]: (k2_partfun1(k4_subset_1(A_4468, C_4464, D_4466), B_4467, k1_tmap_1(A_4468, B_4467, C_4464, D_4466, E_4463, F_4465), C_4464)=E_4463 | ~v1_funct_1(k1_tmap_1(A_4468, B_4467, C_4464, D_4466, E_4463, F_4465)) | k2_partfun1(D_4466, B_4467, F_4465, k9_subset_1(A_4468, C_4464, D_4466))!=k2_partfun1(C_4464, B_4467, E_4463, k9_subset_1(A_4468, C_4464, D_4466)) | ~m1_subset_1(F_4465, k1_zfmisc_1(k2_zfmisc_1(D_4466, B_4467))) | ~v1_funct_2(F_4465, D_4466, B_4467) | ~v1_funct_1(F_4465) | ~m1_subset_1(E_4463, k1_zfmisc_1(k2_zfmisc_1(C_4464, B_4467))) | ~v1_funct_2(E_4463, C_4464, B_4467) | ~v1_funct_1(E_4463) | ~m1_subset_1(D_4466, k1_zfmisc_1(A_4468)) | v1_xboole_0(D_4466) | ~m1_subset_1(C_4464, k1_zfmisc_1(A_4468)) | v1_xboole_0(C_4464) | v1_xboole_0(B_4467) | v1_xboole_0(A_4468))), inference(resolution, [status(thm)], [c_60, c_118479])).
% 27.21/17.99  tff(c_124035, plain, (![A_4468, C_4464, E_4463]: (k2_partfun1(k4_subset_1(A_4468, C_4464, '#skF_5'), '#skF_3', k1_tmap_1(A_4468, '#skF_3', C_4464, '#skF_5', E_4463, '#skF_7'), C_4464)=E_4463 | ~v1_funct_1(k1_tmap_1(A_4468, '#skF_3', C_4464, '#skF_5', E_4463, '#skF_7')) | k2_partfun1(C_4464, '#skF_3', E_4463, k9_subset_1(A_4468, C_4464, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_4468, C_4464, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_4463, k1_zfmisc_1(k2_zfmisc_1(C_4464, '#skF_3'))) | ~v1_funct_2(E_4463, C_4464, '#skF_3') | ~v1_funct_1(E_4463) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4468)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4464, k1_zfmisc_1(A_4468)) | v1_xboole_0(C_4464) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4468))), inference(resolution, [status(thm)], [c_66, c_124029])).
% 27.21/17.99  tff(c_124046, plain, (![A_4468, C_4464, E_4463]: (k2_partfun1(k4_subset_1(A_4468, C_4464, '#skF_5'), '#skF_3', k1_tmap_1(A_4468, '#skF_3', C_4464, '#skF_5', E_4463, '#skF_7'), C_4464)=E_4463 | ~v1_funct_1(k1_tmap_1(A_4468, '#skF_3', C_4464, '#skF_5', E_4463, '#skF_7')) | k2_partfun1(C_4464, '#skF_3', E_4463, k9_subset_1(A_4468, C_4464, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_4468, C_4464, '#skF_5')) | ~m1_subset_1(E_4463, k1_zfmisc_1(k2_zfmisc_1(C_4464, '#skF_3'))) | ~v1_funct_2(E_4463, C_4464, '#skF_3') | ~v1_funct_1(E_4463) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4468)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_4464, k1_zfmisc_1(A_4468)) | v1_xboole_0(C_4464) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4468))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_89855, c_124035])).
% 27.21/17.99  tff(c_134190, plain, (![A_4595, C_4596, E_4597]: (k2_partfun1(k4_subset_1(A_4595, C_4596, '#skF_5'), '#skF_3', k1_tmap_1(A_4595, '#skF_3', C_4596, '#skF_5', E_4597, '#skF_7'), C_4596)=E_4597 | ~v1_funct_1(k1_tmap_1(A_4595, '#skF_3', C_4596, '#skF_5', E_4597, '#skF_7')) | k2_partfun1(C_4596, '#skF_3', E_4597, k9_subset_1(A_4595, C_4596, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_4595, C_4596, '#skF_5')) | ~m1_subset_1(E_4597, k1_zfmisc_1(k2_zfmisc_1(C_4596, '#skF_3'))) | ~v1_funct_2(E_4597, C_4596, '#skF_3') | ~v1_funct_1(E_4597) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4595)) | ~m1_subset_1(C_4596, k1_zfmisc_1(A_4595)) | v1_xboole_0(C_4596) | v1_xboole_0(A_4595))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_124046])).
% 27.21/17.99  tff(c_134195, plain, (![A_4595]: (k2_partfun1(k4_subset_1(A_4595, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4595, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4595, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_4595, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_4595, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4595)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4595)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4595))), inference(resolution, [status(thm)], [c_72, c_134190])).
% 27.21/17.99  tff(c_134206, plain, (![A_4595]: (k2_partfun1(k4_subset_1(A_4595, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4595, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4595, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_4595, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_4595, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4595)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4595)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_4595))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_89852, c_134195])).
% 27.21/17.99  tff(c_135912, plain, (![A_4603]: (k2_partfun1(k4_subset_1(A_4603, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_4603, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4603, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_4603, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_4603, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_4603)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4603)) | v1_xboole_0(A_4603))), inference(negUnitSimplification, [status(thm)], [c_86, c_134206])).
% 27.21/17.99  tff(c_63147, plain, (![A_2763]: (k1_xboole_0=A_2763 | ~v1_partfun1(A_2763, k1_xboole_0) | ~v1_funct_1(A_2763) | ~v4_relat_1(A_2763, k1_xboole_0) | ~v1_relat_1(A_2763))), inference(cnfTransformation, [status(thm)], [f_132])).
% 27.21/17.99  tff(c_63155, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0 | ~v1_partfun1('#skF_1'(k1_xboole_0), k1_xboole_0) | ~v1_funct_1('#skF_1'(k1_xboole_0)) | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_63147])).
% 27.21/17.99  tff(c_63162, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_63155])).
% 27.21/17.99  tff(c_61307, plain, (![B_2634, A_2635]: (k1_relat_1(B_2634)=A_2635 | ~v1_partfun1(B_2634, A_2635) | ~v4_relat_1(B_2634, A_2635) | ~v1_relat_1(B_2634))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.21/17.99  tff(c_61319, plain, (![A_38]: (k1_relat_1('#skF_1'(A_38))=A_38 | ~v1_partfun1('#skF_1'(A_38), A_38) | ~v1_relat_1('#skF_1'(A_38)))), inference(resolution, [status(thm)], [c_46, c_61307])).
% 27.21/17.99  tff(c_61331, plain, (![A_38]: (k1_relat_1('#skF_1'(A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_61319])).
% 27.21/17.99  tff(c_63172, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_63162, c_61331])).
% 27.21/17.99  tff(c_61313, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_61168, c_61307])).
% 27.21/17.99  tff(c_61325, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_61313])).
% 27.21/17.99  tff(c_61362, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_61325])).
% 27.21/17.99  tff(c_62240, plain, (![C_2711, A_2712, B_2713]: (v1_partfun1(C_2711, A_2712) | ~v1_funct_2(C_2711, A_2712, B_2713) | ~v1_funct_1(C_2711) | ~m1_subset_1(C_2711, k1_zfmisc_1(k2_zfmisc_1(A_2712, B_2713))) | v1_xboole_0(B_2713))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.21/17.99  tff(c_62246, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_62240])).
% 27.21/17.99  tff(c_62257, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62246])).
% 27.21/17.99  tff(c_62259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_61362, c_62257])).
% 27.21/17.99  tff(c_62260, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_61325])).
% 27.21/17.99  tff(c_62265, plain, (![B_15]: (k7_relat_1('#skF_7', B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62260, c_14])).
% 27.21/17.99  tff(c_62904, plain, (![B_2750]: (k7_relat_1('#skF_7', B_2750)=k1_xboole_0 | ~r1_xboole_0(B_2750, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_62265])).
% 27.21/17.99  tff(c_62908, plain, (![A_20]: (k7_relat_1('#skF_7', A_20)=k1_xboole_0 | ~r1_subset_1(A_20, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_22, c_62904])).
% 27.21/17.99  tff(c_63059, plain, (![A_2760]: (k7_relat_1('#skF_7', A_2760)=k1_xboole_0 | ~r1_subset_1(A_2760, '#skF_5') | v1_xboole_0(A_2760))), inference(negUnitSimplification, [status(thm)], [c_82, c_62908])).
% 27.21/17.99  tff(c_63062, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_63059])).
% 27.21/17.99  tff(c_63065, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_63062])).
% 27.21/17.99  tff(c_62268, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_7', A_18))=k3_xboole_0('#skF_5', A_18) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62260, c_18])).
% 27.21/17.99  tff(c_62277, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_7', A_18))=k3_xboole_0('#skF_5', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_62268])).
% 27.21/17.99  tff(c_63069, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63065, c_62277])).
% 27.21/17.99  tff(c_62955, plain, (![B_2754, A_2755]: (k7_relat_1(B_2754, k3_xboole_0(k1_relat_1(B_2754), A_2755))=k7_relat_1(B_2754, A_2755) | ~v1_relat_1(B_2754))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.21/17.99  tff(c_62988, plain, (![A_2755]: (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', A_2755))=k7_relat_1('#skF_7', A_2755) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62260, c_62955])).
% 27.21/17.99  tff(c_63006, plain, (![A_2755]: (k7_relat_1('#skF_7', k3_xboole_0('#skF_5', A_2755))=k7_relat_1('#skF_7', A_2755))), inference(demodulation, [status(thm), theory('equality')], [c_61154, c_62988])).
% 27.21/17.99  tff(c_63076, plain, (k7_relat_1('#skF_7', k1_relat_1(k1_xboole_0))=k7_relat_1('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63069, c_63006])).
% 27.21/17.99  tff(c_63079, plain, (k7_relat_1('#skF_7', k1_relat_1(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_63065, c_63076])).
% 27.21/17.99  tff(c_63196, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_63172, c_63079])).
% 27.21/17.99  tff(c_63197, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_63172, c_63069])).
% 27.21/17.99  tff(c_61332, plain, (![A_2636]: (k1_relat_1('#skF_1'(A_2636))=A_2636)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_61319])).
% 27.21/17.99  tff(c_61338, plain, (![A_2636, B_15]: (k7_relat_1('#skF_1'(A_2636), B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, A_2636) | ~v1_relat_1('#skF_1'(A_2636)))), inference(superposition, [status(thm), theory('equality')], [c_61332, c_14])).
% 27.21/17.99  tff(c_63009, plain, (![A_2756, B_2757]: (k7_relat_1('#skF_1'(A_2756), B_2757)=k1_xboole_0 | ~r1_xboole_0(B_2757, A_2756))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_61338])).
% 27.21/17.99  tff(c_61341, plain, (![A_2636, A_18]: (k1_relat_1(k7_relat_1('#skF_1'(A_2636), A_18))=k3_xboole_0(A_2636, A_18) | ~v1_relat_1('#skF_1'(A_2636)))), inference(superposition, [status(thm), theory('equality')], [c_61332, c_18])).
% 27.21/17.99  tff(c_61352, plain, (![A_2636, A_18]: (k1_relat_1(k7_relat_1('#skF_1'(A_2636), A_18))=k3_xboole_0(A_2636, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_61341])).
% 27.21/17.99  tff(c_63019, plain, (![A_2756, B_2757]: (k3_xboole_0(A_2756, B_2757)=k1_relat_1(k1_xboole_0) | ~r1_xboole_0(B_2757, A_2756))), inference(superposition, [status(thm), theory('equality')], [c_63009, c_61352])).
% 27.21/17.99  tff(c_63383, plain, (![A_2778, B_2779]: (k3_xboole_0(A_2778, B_2779)=k1_xboole_0 | ~r1_xboole_0(B_2779, A_2778))), inference(demodulation, [status(thm), theory('equality')], [c_63172, c_63019])).
% 27.21/17.99  tff(c_63393, plain, (![B_2780, A_2781]: (k3_xboole_0(B_2780, A_2781)=k1_xboole_0 | k3_xboole_0(A_2781, B_2780)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_63383])).
% 27.21/17.99  tff(c_63403, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_63197, c_63393])).
% 27.21/17.99  tff(c_61316, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_61167, c_61307])).
% 27.21/17.99  tff(c_61328, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61153, c_61316])).
% 27.21/17.99  tff(c_62291, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_61328])).
% 27.21/17.99  tff(c_62830, plain, (![C_2745, A_2746, B_2747]: (v1_partfun1(C_2745, A_2746) | ~v1_funct_2(C_2745, A_2746, B_2747) | ~v1_funct_1(C_2745) | ~m1_subset_1(C_2745, k1_zfmisc_1(k2_zfmisc_1(A_2746, B_2747))) | v1_xboole_0(B_2747))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.21/17.99  tff(c_62833, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_62830])).
% 27.21/17.99  tff(c_62843, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62833])).
% 27.21/17.99  tff(c_62845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_62291, c_62843])).
% 27.21/17.99  tff(c_62846, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_61328])).
% 27.21/17.99  tff(c_62985, plain, (![A_2755]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_2755))=k7_relat_1('#skF_6', A_2755) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_62846, c_62955])).
% 27.21/17.99  tff(c_63004, plain, (![A_2755]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_2755))=k7_relat_1('#skF_6', A_2755))), inference(demodulation, [status(thm), theory('equality')], [c_61153, c_62985])).
% 27.21/17.99  tff(c_63308, plain, (![A_2768, B_2769, C_2770, D_2771]: (k2_partfun1(A_2768, B_2769, C_2770, D_2771)=k7_relat_1(C_2770, D_2771) | ~m1_subset_1(C_2770, k1_zfmisc_1(k2_zfmisc_1(A_2768, B_2769))) | ~v1_funct_1(C_2770))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.21/17.99  tff(c_63310, plain, (![D_2771]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_2771)=k7_relat_1('#skF_6', D_2771) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_63308])).
% 27.21/17.99  tff(c_63318, plain, (![D_2771]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_2771)=k7_relat_1('#skF_6', D_2771))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_63310])).
% 27.21/17.99  tff(c_61254, plain, (![A_2626, B_2627, C_2628]: (k9_subset_1(A_2626, B_2627, C_2628)=k3_xboole_0(B_2627, C_2628) | ~m1_subset_1(C_2628, k1_zfmisc_1(A_2626)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.21/17.99  tff(c_61267, plain, (![B_2627]: (k9_subset_1('#skF_2', B_2627, '#skF_5')=k3_xboole_0(B_2627, '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_61254])).
% 27.21/17.99  tff(c_61270, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61267, c_61267, c_7026])).
% 27.21/17.99  tff(c_63325, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_63318, c_61270])).
% 27.21/17.99  tff(c_63326, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63004, c_63325])).
% 27.21/17.99  tff(c_63312, plain, (![D_2771]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2771)=k7_relat_1('#skF_7', D_2771) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_63308])).
% 27.21/17.99  tff(c_63321, plain, (![D_2771]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2771)=k7_relat_1('#skF_7', D_2771))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_63312])).
% 27.21/17.99  tff(c_63357, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))=k7_relat_1('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_63326, c_63321])).
% 27.21/17.99  tff(c_63488, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_63196, c_63403, c_63357])).
% 27.21/17.99  tff(c_63413, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_63403, c_63004])).
% 27.21/17.99  tff(c_63512, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_63488, c_63413])).
% 27.21/17.99  tff(c_63546, plain, (![E_2785, D_2788, C_2786, F_2787, A_2790, B_2789]: (v1_funct_1(k1_tmap_1(A_2790, B_2789, C_2786, D_2788, E_2785, F_2787)) | ~m1_subset_1(F_2787, k1_zfmisc_1(k2_zfmisc_1(D_2788, B_2789))) | ~v1_funct_2(F_2787, D_2788, B_2789) | ~v1_funct_1(F_2787) | ~m1_subset_1(E_2785, k1_zfmisc_1(k2_zfmisc_1(C_2786, B_2789))) | ~v1_funct_2(E_2785, C_2786, B_2789) | ~v1_funct_1(E_2785) | ~m1_subset_1(D_2788, k1_zfmisc_1(A_2790)) | v1_xboole_0(D_2788) | ~m1_subset_1(C_2786, k1_zfmisc_1(A_2790)) | v1_xboole_0(C_2786) | v1_xboole_0(B_2789) | v1_xboole_0(A_2790))), inference(cnfTransformation, [status(thm)], [f_214])).
% 27.21/17.99  tff(c_63550, plain, (![A_2790, C_2786, E_2785]: (v1_funct_1(k1_tmap_1(A_2790, '#skF_3', C_2786, '#skF_5', E_2785, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2785, k1_zfmisc_1(k2_zfmisc_1(C_2786, '#skF_3'))) | ~v1_funct_2(E_2785, C_2786, '#skF_3') | ~v1_funct_1(E_2785) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2790)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2786, k1_zfmisc_1(A_2790)) | v1_xboole_0(C_2786) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2790))), inference(resolution, [status(thm)], [c_66, c_63546])).
% 27.21/17.99  tff(c_63560, plain, (![A_2790, C_2786, E_2785]: (v1_funct_1(k1_tmap_1(A_2790, '#skF_3', C_2786, '#skF_5', E_2785, '#skF_7')) | ~m1_subset_1(E_2785, k1_zfmisc_1(k2_zfmisc_1(C_2786, '#skF_3'))) | ~v1_funct_2(E_2785, C_2786, '#skF_3') | ~v1_funct_1(E_2785) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2790)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2786, k1_zfmisc_1(A_2790)) | v1_xboole_0(C_2786) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2790))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_63550])).
% 27.21/17.99  tff(c_64203, plain, (![A_2832, C_2833, E_2834]: (v1_funct_1(k1_tmap_1(A_2832, '#skF_3', C_2833, '#skF_5', E_2834, '#skF_7')) | ~m1_subset_1(E_2834, k1_zfmisc_1(k2_zfmisc_1(C_2833, '#skF_3'))) | ~v1_funct_2(E_2834, C_2833, '#skF_3') | ~v1_funct_1(E_2834) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2832)) | ~m1_subset_1(C_2833, k1_zfmisc_1(A_2832)) | v1_xboole_0(C_2833) | v1_xboole_0(A_2832))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_63560])).
% 27.21/17.99  tff(c_64208, plain, (![A_2832]: (v1_funct_1(k1_tmap_1(A_2832, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2832)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2832)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2832))), inference(resolution, [status(thm)], [c_72, c_64203])).
% 27.21/17.99  tff(c_64219, plain, (![A_2832]: (v1_funct_1(k1_tmap_1(A_2832, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2832)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2832)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2832))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64208])).
% 27.21/17.99  tff(c_64719, plain, (![A_2853]: (v1_funct_1(k1_tmap_1(A_2853, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2853)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2853)) | v1_xboole_0(A_2853))), inference(negUnitSimplification, [status(thm)], [c_86, c_64219])).
% 27.21/17.99  tff(c_64722, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_64719])).
% 27.21/17.99  tff(c_64725, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64722])).
% 27.21/17.99  tff(c_64726, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_90, c_64725])).
% 27.21/17.99  tff(c_64022, plain, (![E_2819, A_2815, F_2820, B_2818, C_2817, D_2816]: (k2_partfun1(k4_subset_1(A_2815, C_2817, D_2816), B_2818, k1_tmap_1(A_2815, B_2818, C_2817, D_2816, E_2819, F_2820), D_2816)=F_2820 | ~m1_subset_1(k1_tmap_1(A_2815, B_2818, C_2817, D_2816, E_2819, F_2820), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2815, C_2817, D_2816), B_2818))) | ~v1_funct_2(k1_tmap_1(A_2815, B_2818, C_2817, D_2816, E_2819, F_2820), k4_subset_1(A_2815, C_2817, D_2816), B_2818) | ~v1_funct_1(k1_tmap_1(A_2815, B_2818, C_2817, D_2816, E_2819, F_2820)) | k2_partfun1(D_2816, B_2818, F_2820, k9_subset_1(A_2815, C_2817, D_2816))!=k2_partfun1(C_2817, B_2818, E_2819, k9_subset_1(A_2815, C_2817, D_2816)) | ~m1_subset_1(F_2820, k1_zfmisc_1(k2_zfmisc_1(D_2816, B_2818))) | ~v1_funct_2(F_2820, D_2816, B_2818) | ~v1_funct_1(F_2820) | ~m1_subset_1(E_2819, k1_zfmisc_1(k2_zfmisc_1(C_2817, B_2818))) | ~v1_funct_2(E_2819, C_2817, B_2818) | ~v1_funct_1(E_2819) | ~m1_subset_1(D_2816, k1_zfmisc_1(A_2815)) | v1_xboole_0(D_2816) | ~m1_subset_1(C_2817, k1_zfmisc_1(A_2815)) | v1_xboole_0(C_2817) | v1_xboole_0(B_2818) | v1_xboole_0(A_2815))), inference(cnfTransformation, [status(thm)], [f_180])).
% 27.21/17.99  tff(c_68723, plain, (![D_3014, E_3011, F_3013, B_3015, C_3012, A_3016]: (k2_partfun1(k4_subset_1(A_3016, C_3012, D_3014), B_3015, k1_tmap_1(A_3016, B_3015, C_3012, D_3014, E_3011, F_3013), D_3014)=F_3013 | ~v1_funct_2(k1_tmap_1(A_3016, B_3015, C_3012, D_3014, E_3011, F_3013), k4_subset_1(A_3016, C_3012, D_3014), B_3015) | ~v1_funct_1(k1_tmap_1(A_3016, B_3015, C_3012, D_3014, E_3011, F_3013)) | k2_partfun1(D_3014, B_3015, F_3013, k9_subset_1(A_3016, C_3012, D_3014))!=k2_partfun1(C_3012, B_3015, E_3011, k9_subset_1(A_3016, C_3012, D_3014)) | ~m1_subset_1(F_3013, k1_zfmisc_1(k2_zfmisc_1(D_3014, B_3015))) | ~v1_funct_2(F_3013, D_3014, B_3015) | ~v1_funct_1(F_3013) | ~m1_subset_1(E_3011, k1_zfmisc_1(k2_zfmisc_1(C_3012, B_3015))) | ~v1_funct_2(E_3011, C_3012, B_3015) | ~v1_funct_1(E_3011) | ~m1_subset_1(D_3014, k1_zfmisc_1(A_3016)) | v1_xboole_0(D_3014) | ~m1_subset_1(C_3012, k1_zfmisc_1(A_3016)) | v1_xboole_0(C_3012) | v1_xboole_0(B_3015) | v1_xboole_0(A_3016))), inference(resolution, [status(thm)], [c_58, c_64022])).
% 27.21/17.99  tff(c_75130, plain, (![B_3231, A_3232, C_3228, E_3227, D_3230, F_3229]: (k2_partfun1(k4_subset_1(A_3232, C_3228, D_3230), B_3231, k1_tmap_1(A_3232, B_3231, C_3228, D_3230, E_3227, F_3229), D_3230)=F_3229 | ~v1_funct_1(k1_tmap_1(A_3232, B_3231, C_3228, D_3230, E_3227, F_3229)) | k2_partfun1(D_3230, B_3231, F_3229, k9_subset_1(A_3232, C_3228, D_3230))!=k2_partfun1(C_3228, B_3231, E_3227, k9_subset_1(A_3232, C_3228, D_3230)) | ~m1_subset_1(F_3229, k1_zfmisc_1(k2_zfmisc_1(D_3230, B_3231))) | ~v1_funct_2(F_3229, D_3230, B_3231) | ~v1_funct_1(F_3229) | ~m1_subset_1(E_3227, k1_zfmisc_1(k2_zfmisc_1(C_3228, B_3231))) | ~v1_funct_2(E_3227, C_3228, B_3231) | ~v1_funct_1(E_3227) | ~m1_subset_1(D_3230, k1_zfmisc_1(A_3232)) | v1_xboole_0(D_3230) | ~m1_subset_1(C_3228, k1_zfmisc_1(A_3232)) | v1_xboole_0(C_3228) | v1_xboole_0(B_3231) | v1_xboole_0(A_3232))), inference(resolution, [status(thm)], [c_60, c_68723])).
% 27.21/17.99  tff(c_75136, plain, (![A_3232, C_3228, E_3227]: (k2_partfun1(k4_subset_1(A_3232, C_3228, '#skF_5'), '#skF_3', k1_tmap_1(A_3232, '#skF_3', C_3228, '#skF_5', E_3227, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3232, '#skF_3', C_3228, '#skF_5', E_3227, '#skF_7')) | k2_partfun1(C_3228, '#skF_3', E_3227, k9_subset_1(A_3232, C_3228, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_3232, C_3228, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3227, k1_zfmisc_1(k2_zfmisc_1(C_3228, '#skF_3'))) | ~v1_funct_2(E_3227, C_3228, '#skF_3') | ~v1_funct_1(E_3227) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3232)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3228, k1_zfmisc_1(A_3232)) | v1_xboole_0(C_3228) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3232))), inference(resolution, [status(thm)], [c_66, c_75130])).
% 27.21/17.99  tff(c_75147, plain, (![A_3232, C_3228, E_3227]: (k2_partfun1(k4_subset_1(A_3232, C_3228, '#skF_5'), '#skF_3', k1_tmap_1(A_3232, '#skF_3', C_3228, '#skF_5', E_3227, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3232, '#skF_3', C_3228, '#skF_5', E_3227, '#skF_7')) | k2_partfun1(C_3228, '#skF_3', E_3227, k9_subset_1(A_3232, C_3228, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3232, C_3228, '#skF_5')) | ~m1_subset_1(E_3227, k1_zfmisc_1(k2_zfmisc_1(C_3228, '#skF_3'))) | ~v1_funct_2(E_3227, C_3228, '#skF_3') | ~v1_funct_1(E_3227) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3232)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3228, k1_zfmisc_1(A_3232)) | v1_xboole_0(C_3228) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3232))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_63321, c_75136])).
% 27.21/17.99  tff(c_86548, plain, (![A_3379, C_3380, E_3381]: (k2_partfun1(k4_subset_1(A_3379, C_3380, '#skF_5'), '#skF_3', k1_tmap_1(A_3379, '#skF_3', C_3380, '#skF_5', E_3381, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3379, '#skF_3', C_3380, '#skF_5', E_3381, '#skF_7')) | k2_partfun1(C_3380, '#skF_3', E_3381, k9_subset_1(A_3379, C_3380, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3379, C_3380, '#skF_5')) | ~m1_subset_1(E_3381, k1_zfmisc_1(k2_zfmisc_1(C_3380, '#skF_3'))) | ~v1_funct_2(E_3381, C_3380, '#skF_3') | ~v1_funct_1(E_3381) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3379)) | ~m1_subset_1(C_3380, k1_zfmisc_1(A_3379)) | v1_xboole_0(C_3380) | v1_xboole_0(A_3379))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_75147])).
% 27.21/17.99  tff(c_86553, plain, (![A_3379]: (k2_partfun1(k4_subset_1(A_3379, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3379, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3379, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_3379, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3379, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3379)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3379)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3379))), inference(resolution, [status(thm)], [c_72, c_86548])).
% 27.21/17.99  tff(c_86564, plain, (![A_3379]: (k2_partfun1(k4_subset_1(A_3379, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3379, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3379, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3379, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_3379, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3379)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3379)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3379))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_63318, c_86553])).
% 27.21/17.99  tff(c_87697, plain, (![A_3388]: (k2_partfun1(k4_subset_1(A_3388, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3388, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3388, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3388, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_3388, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3388)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3388)) | v1_xboole_0(A_3388))), inference(negUnitSimplification, [status(thm)], [c_86, c_86564])).
% 27.21/17.99  tff(c_7025, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_64])).
% 27.21/17.99  tff(c_61253, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_7025])).
% 27.21/17.99  tff(c_87708, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87697, c_61253])).
% 27.21/17.99  tff(c_87722, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_63512, c_63403, c_61267, c_63196, c_63403, c_61267, c_64726, c_87708])).
% 27.21/17.99  tff(c_87724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_87722])).
% 27.21/17.99  tff(c_87725, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_7025])).
% 27.21/17.99  tff(c_135924, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135912, c_87725])).
% 27.21/17.99  tff(c_135938, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_90094, c_89984, c_87740, c_89727, c_89984, c_87740, c_90802, c_135924])).
% 27.21/17.99  tff(c_135940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_135938])).
% 27.21/17.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.21/17.99  
% 27.21/17.99  Inference rules
% 27.21/17.99  ----------------------
% 27.21/17.99  #Ref     : 1
% 27.21/17.99  #Sup     : 32848
% 27.21/17.99  #Fact    : 0
% 27.21/17.99  #Define  : 0
% 27.21/17.99  #Split   : 67
% 27.21/17.99  #Chain   : 0
% 27.21/17.99  #Close   : 0
% 27.21/17.99  
% 27.21/17.99  Ordering : KBO
% 27.21/17.99  
% 27.21/17.99  Simplification rules
% 27.21/17.99  ----------------------
% 27.21/17.99  #Subsume      : 12111
% 27.21/17.99  #Demod        : 43779
% 27.21/17.99  #Tautology    : 11912
% 27.21/17.99  #SimpNegUnit  : 771
% 27.21/17.99  #BackRed      : 148
% 27.21/17.99  
% 27.21/17.99  #Partial instantiations: 0
% 27.21/17.99  #Strategies tried      : 1
% 27.21/17.99  
% 27.21/17.99  Timing (in seconds)
% 27.21/17.99  ----------------------
% 27.21/18.00  Preprocessing        : 0.45
% 27.21/18.00  Parsing              : 0.23
% 27.21/18.00  CNF conversion       : 0.06
% 27.21/18.00  Main loop            : 16.68
% 27.21/18.00  Inferencing          : 3.48
% 27.21/18.00  Reduction            : 7.06
% 27.21/18.00  Demodulation         : 5.76
% 27.21/18.00  BG Simplification    : 0.33
% 27.21/18.00  Subsumption          : 5.15
% 27.21/18.00  Abstraction          : 0.54
% 27.21/18.00  MUC search           : 0.00
% 27.21/18.00  Cooper               : 0.00
% 27.21/18.00  Total                : 17.24
% 27.21/18.00  Index Insertion      : 0.00
% 27.21/18.00  Index Deletion       : 0.00
% 27.21/18.00  Index Matching       : 0.00
% 27.21/18.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
