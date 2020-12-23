%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 376 expanded)
%              Number of leaves         :   40 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  326 (1674 expanded)
%              Number of equality atoms :   62 ( 230 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_82,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_105,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_319,plain,(
    ! [A_143,C_144,E_142,D_146,B_145,F_147] :
      ( k1_funct_1(k8_funct_2(B_145,C_144,A_143,D_146,E_142),F_147) = k1_funct_1(E_142,k1_funct_1(D_146,F_147))
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(B_145,C_144,D_146),k1_relset_1(C_144,A_143,E_142))
      | ~ m1_subset_1(F_147,B_145)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(C_144,A_143)))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(B_145,C_144)))
      | ~ v1_funct_2(D_146,B_145,C_144)
      | ~ v1_funct_1(D_146)
      | v1_xboole_0(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_327,plain,(
    ! [A_143,E_142,F_147] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_143,'#skF_4',E_142),F_147) = k1_funct_1(E_142,k1_funct_1('#skF_4',F_147))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_143,E_142))
      | ~ m1_subset_1(F_147,'#skF_2')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_143)))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_319])).

tff(c_337,plain,(
    ! [A_143,E_142,F_147] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_143,'#skF_4',E_142),F_147) = k1_funct_1(E_142,k1_funct_1('#skF_4',F_147))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_143,E_142))
      | ~ m1_subset_1(F_147,'#skF_2')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_143)))
      | ~ v1_funct_1(E_142)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_327])).

tff(c_338,plain,(
    ! [A_143,E_142,F_147] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_143,'#skF_4',E_142),F_147) = k1_funct_1(E_142,k1_funct_1('#skF_4',F_147))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_143,E_142))
      | ~ m1_subset_1(F_147,'#skF_2')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_143)))
      | ~ v1_funct_1(E_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_337])).

tff(c_365,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_367,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_2])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_367])).

tff(c_371,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_60,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_36,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_92,plain,(
    ! [B_89,A_90] :
      ( k1_relat_1(B_89) = A_90
      | ~ v1_partfun1(B_89,A_90)
      | ~ v4_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_95,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_75,c_92])).

tff(c_101,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_95])).

tff(c_132,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_132])).

tff(c_141,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_138])).

tff(c_323,plain,(
    ! [B_145,D_146,F_147] :
      ( k1_funct_1(k8_funct_2(B_145,'#skF_1','#skF_3',D_146,'#skF_5'),F_147) = k1_funct_1('#skF_5',k1_funct_1(D_146,F_147))
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(B_145,'#skF_1',D_146),'#skF_1')
      | ~ m1_subset_1(F_147,B_145)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(B_145,'#skF_1')))
      | ~ v1_funct_2(D_146,B_145,'#skF_1')
      | ~ v1_funct_1(D_146)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_319])).

tff(c_332,plain,(
    ! [B_145,D_146,F_147] :
      ( k1_funct_1(k8_funct_2(B_145,'#skF_1','#skF_3',D_146,'#skF_5'),F_147) = k1_funct_1('#skF_5',k1_funct_1(D_146,F_147))
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(B_145,'#skF_1',D_146),'#skF_1')
      | ~ m1_subset_1(F_147,B_145)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(B_145,'#skF_1')))
      | ~ v1_funct_2(D_146,B_145,'#skF_1')
      | ~ v1_funct_1(D_146)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_323])).

tff(c_395,plain,(
    ! [B_159,D_160,F_161] :
      ( k1_funct_1(k8_funct_2(B_159,'#skF_1','#skF_3',D_160,'#skF_5'),F_161) = k1_funct_1('#skF_5',k1_funct_1(D_160,F_161))
      | k1_xboole_0 = B_159
      | ~ r1_tarski(k2_relset_1(B_159,'#skF_1',D_160),'#skF_1')
      | ~ m1_subset_1(F_161,B_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_1')))
      | ~ v1_funct_2(D_160,B_159,'#skF_1')
      | ~ v1_funct_1(D_160) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_332])).

tff(c_400,plain,(
    ! [F_161] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_161) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_161))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_161,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_395])).

tff(c_404,plain,(
    ! [F_161] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_161) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_161))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_161,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_112,c_400])).

tff(c_405,plain,(
    ! [F_161] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_161) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_161))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_161,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_404])).

tff(c_406,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_409,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_406])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_89,c_409])).

tff(c_414,plain,(
    ! [F_161] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_161) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_161))
      | ~ m1_subset_1(F_161,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_162,plain,(
    ! [B_103,C_101,A_104,D_105,E_102] :
      ( v1_funct_1(k8_funct_2(A_104,B_103,C_101,D_105,E_102))
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(B_103,C_101)))
      | ~ v1_funct_1(E_102)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_2(D_105,A_104,B_103)
      | ~ v1_funct_1(D_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,(
    ! [A_104,D_105] :
      ( v1_funct_1(k8_funct_2(A_104,'#skF_1','#skF_3',D_105,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_104,'#skF_1')))
      | ~ v1_funct_2(D_105,A_104,'#skF_1')
      | ~ v1_funct_1(D_105) ) ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_174,plain,(
    ! [A_108,D_109] :
      ( v1_funct_1(k8_funct_2(A_108,'#skF_1','#skF_3',D_109,'#skF_5'))
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_108,'#skF_1')))
      | ~ v1_funct_2(D_109,A_108,'#skF_1')
      | ~ v1_funct_1(D_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_177,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_180,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_177])).

tff(c_193,plain,(
    ! [D_116,B_114,A_115,C_112,E_113] :
      ( v1_funct_2(k8_funct_2(A_115,B_114,C_112,D_116,E_113),A_115,C_112)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(B_114,C_112)))
      | ~ v1_funct_1(E_113)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_2(D_116,A_115,B_114)
      | ~ v1_funct_1(D_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_197,plain,(
    ! [A_115,D_116] :
      ( v1_funct_2(k8_funct_2(A_115,'#skF_1','#skF_3',D_116,'#skF_5'),A_115,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_115,'#skF_1')))
      | ~ v1_funct_2(D_116,A_115,'#skF_1')
      | ~ v1_funct_1(D_116) ) ),
    inference(resolution,[status(thm)],[c_40,c_193])).

tff(c_205,plain,(
    ! [A_119,D_120] :
      ( v1_funct_2(k8_funct_2(A_119,'#skF_1','#skF_3',D_120,'#skF_5'),A_119,'#skF_3')
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_119,'#skF_1')))
      | ~ v1_funct_2(D_120,A_119,'#skF_1')
      | ~ v1_funct_1(D_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_197])).

tff(c_207,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_205])).

tff(c_210,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_207])).

tff(c_24,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] :
      ( m1_subset_1(k8_funct_2(A_19,B_20,C_21,D_22,E_23),k1_zfmisc_1(k2_zfmisc_1(A_19,C_21)))
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(B_20,C_21)))
      | ~ v1_funct_1(E_23)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(D_22,A_19,B_20)
      | ~ v1_funct_1(D_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_211,plain,(
    ! [C_121,A_124,E_122,D_125,B_123] :
      ( m1_subset_1(k8_funct_2(A_124,B_123,C_121,D_125,E_122),k1_zfmisc_1(k2_zfmisc_1(A_124,C_121)))
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(B_123,C_121)))
      | ~ v1_funct_1(E_122)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(D_125,A_124,B_123)
      | ~ v1_funct_1(D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_442,plain,(
    ! [C_169,E_166,A_167,D_168,B_170] :
      ( k1_relset_1(A_167,C_169,k8_funct_2(A_167,B_170,C_169,D_168,E_166)) = k1_relat_1(k8_funct_2(A_167,B_170,C_169,D_168,E_166))
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(B_170,C_169)))
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_167,B_170)))
      | ~ v1_funct_2(D_168,A_167,B_170)
      | ~ v1_funct_1(D_168) ) ),
    inference(resolution,[status(thm)],[c_211,c_16])).

tff(c_448,plain,(
    ! [A_167,D_168] :
      ( k1_relset_1(A_167,'#skF_3',k8_funct_2(A_167,'#skF_1','#skF_3',D_168,'#skF_5')) = k1_relat_1(k8_funct_2(A_167,'#skF_1','#skF_3',D_168,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_167,'#skF_1')))
      | ~ v1_funct_2(D_168,A_167,'#skF_1')
      | ~ v1_funct_1(D_168) ) ),
    inference(resolution,[status(thm)],[c_40,c_442])).

tff(c_461,plain,(
    ! [A_173,D_174] :
      ( k1_relset_1(A_173,'#skF_3',k8_funct_2(A_173,'#skF_1','#skF_3',D_174,'#skF_5')) = k1_relat_1(k8_funct_2(A_173,'#skF_1','#skF_3',D_174,'#skF_5'))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_173,'#skF_1')))
      | ~ v1_funct_2(D_174,A_173,'#skF_1')
      | ~ v1_funct_1(D_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_448])).

tff(c_466,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_461])).

tff(c_470,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_466])).

tff(c_32,plain,(
    ! [C_30,F_44,D_38,B_29,E_42,A_28] :
      ( k1_funct_1(k8_funct_2(B_29,C_30,A_28,D_38,E_42),F_44) = k1_funct_1(E_42,k1_funct_1(D_38,F_44))
      | k1_xboole_0 = B_29
      | ~ r1_tarski(k2_relset_1(B_29,C_30,D_38),k1_relset_1(C_30,A_28,E_42))
      | ~ m1_subset_1(F_44,B_29)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(C_30,A_28)))
      | ~ v1_funct_1(E_42)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_29,C_30)))
      | ~ v1_funct_2(D_38,B_29,C_30)
      | ~ v1_funct_1(D_38)
      | v1_xboole_0(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_473,plain,(
    ! [B_29,D_38,F_44] :
      ( k1_funct_1(k8_funct_2(B_29,'#skF_2','#skF_3',D_38,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_44) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_38,F_44))
      | k1_xboole_0 = B_29
      | ~ r1_tarski(k2_relset_1(B_29,'#skF_2',D_38),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_44,B_29)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_29,'#skF_2')))
      | ~ v1_funct_2(D_38,B_29,'#skF_2')
      | ~ v1_funct_1(D_38)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_32])).

tff(c_477,plain,(
    ! [B_29,D_38,F_44] :
      ( k1_funct_1(k8_funct_2(B_29,'#skF_2','#skF_3',D_38,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_44) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_38,F_44))
      | k1_xboole_0 = B_29
      | ~ r1_tarski(k2_relset_1(B_29,'#skF_2',D_38),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_44,B_29)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_29,'#skF_2')))
      | ~ v1_funct_2(D_38,B_29,'#skF_2')
      | ~ v1_funct_1(D_38)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_473])).

tff(c_478,plain,(
    ! [B_29,D_38,F_44] :
      ( k1_funct_1(k8_funct_2(B_29,'#skF_2','#skF_3',D_38,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_44) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_38,F_44))
      | k1_xboole_0 = B_29
      | ~ r1_tarski(k2_relset_1(B_29,'#skF_2',D_38),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_44,B_29)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_29,'#skF_2')))
      | ~ v1_funct_2(D_38,B_29,'#skF_2')
      | ~ v1_funct_1(D_38) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_477])).

tff(c_558,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_561,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_558])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_561])).

tff(c_567,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_150,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k3_funct_2(A_97,B_98,C_99,D_100) = k1_funct_1(C_99,D_100)
      | ~ m1_subset_1(D_100,A_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(C_99,A_97,B_98)
      | ~ v1_funct_1(C_99)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_156,plain,(
    ! [B_98,C_99] :
      ( k3_funct_2('#skF_2',B_98,C_99,'#skF_6') = k1_funct_1(C_99,'#skF_6')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_98)))
      | ~ v1_funct_2(C_99,'#skF_2',B_98)
      | ~ v1_funct_1(C_99)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_161,plain,(
    ! [B_98,C_99] :
      ( k3_funct_2('#skF_2',B_98,C_99,'#skF_6') = k1_funct_1(C_99,'#skF_6')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_98)))
      | ~ v1_funct_2(C_99,'#skF_2',B_98)
      | ~ v1_funct_1(C_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_156])).

tff(c_586,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_567,c_161])).

tff(c_632,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_210,c_586])).

tff(c_181,plain,(
    ! [B_110,C_111] :
      ( k3_funct_2('#skF_2',B_110,C_111,'#skF_6') = k1_funct_1(C_111,'#skF_6')
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_110)))
      | ~ v1_funct_2(C_111,'#skF_2',B_110)
      | ~ v1_funct_1(C_111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_156])).

tff(c_184,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_181])).

tff(c_187,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_184])).

tff(c_34,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_188,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_34])).

tff(c_648,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_188])).

tff(c_655,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_648])).

tff(c_659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.46  
% 3.34/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.34/1.47  
% 3.34/1.47  %Foreground sorts:
% 3.34/1.47  
% 3.34/1.47  
% 3.34/1.47  %Background operators:
% 3.34/1.47  
% 3.34/1.47  
% 3.34/1.47  %Foreground operators:
% 3.34/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.47  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.34/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.34/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.34/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.34/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.34/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.47  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.34/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.47  
% 3.34/1.49  tff(f_143, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 3.34/1.49  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.34/1.49  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.34/1.49  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.34/1.49  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.34/1.49  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.49  tff(f_116, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.34/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.34/1.49  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.34/1.49  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.34/1.49  tff(f_79, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 3.34/1.49  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.34/1.49  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.49  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_54, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.49  tff(c_57, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_54])).
% 3.34/1.49  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_57])).
% 3.34/1.49  tff(c_82, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.49  tff(c_89, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_82])).
% 3.34/1.49  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.49  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_105, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.34/1.49  tff(c_112, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_105])).
% 3.34/1.49  tff(c_319, plain, (![A_143, C_144, E_142, D_146, B_145, F_147]: (k1_funct_1(k8_funct_2(B_145, C_144, A_143, D_146, E_142), F_147)=k1_funct_1(E_142, k1_funct_1(D_146, F_147)) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(B_145, C_144, D_146), k1_relset_1(C_144, A_143, E_142)) | ~m1_subset_1(F_147, B_145) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(C_144, A_143))) | ~v1_funct_1(E_142) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(B_145, C_144))) | ~v1_funct_2(D_146, B_145, C_144) | ~v1_funct_1(D_146) | v1_xboole_0(C_144))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.34/1.49  tff(c_327, plain, (![A_143, E_142, F_147]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_143, '#skF_4', E_142), F_147)=k1_funct_1(E_142, k1_funct_1('#skF_4', F_147)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_143, E_142)) | ~m1_subset_1(F_147, '#skF_2') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_143))) | ~v1_funct_1(E_142) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_319])).
% 3.34/1.49  tff(c_337, plain, (![A_143, E_142, F_147]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_143, '#skF_4', E_142), F_147)=k1_funct_1(E_142, k1_funct_1('#skF_4', F_147)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_143, E_142)) | ~m1_subset_1(F_147, '#skF_2') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_143))) | ~v1_funct_1(E_142) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_327])).
% 3.34/1.49  tff(c_338, plain, (![A_143, E_142, F_147]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_143, '#skF_4', E_142), F_147)=k1_funct_1(E_142, k1_funct_1('#skF_4', F_147)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_143, E_142)) | ~m1_subset_1(F_147, '#skF_2') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_143))) | ~v1_funct_1(E_142))), inference(negUnitSimplification, [status(thm)], [c_52, c_337])).
% 3.34/1.49  tff(c_365, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_338])).
% 3.34/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.34/1.49  tff(c_367, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_2])).
% 3.34/1.49  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_367])).
% 3.34/1.49  tff(c_371, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_338])).
% 3.34/1.49  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_60, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_54])).
% 3.34/1.49  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_60])).
% 3.34/1.49  tff(c_36, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_67, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.49  tff(c_75, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_67])).
% 3.34/1.49  tff(c_92, plain, (![B_89, A_90]: (k1_relat_1(B_89)=A_90 | ~v1_partfun1(B_89, A_90) | ~v4_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.49  tff(c_95, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_75, c_92])).
% 3.34/1.49  tff(c_101, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_95])).
% 3.34/1.49  tff(c_132, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.49  tff(c_138, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_132])).
% 3.34/1.49  tff(c_141, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_138])).
% 3.34/1.49  tff(c_323, plain, (![B_145, D_146, F_147]: (k1_funct_1(k8_funct_2(B_145, '#skF_1', '#skF_3', D_146, '#skF_5'), F_147)=k1_funct_1('#skF_5', k1_funct_1(D_146, F_147)) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(B_145, '#skF_1', D_146), '#skF_1') | ~m1_subset_1(F_147, B_145) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(B_145, '#skF_1'))) | ~v1_funct_2(D_146, B_145, '#skF_1') | ~v1_funct_1(D_146) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_319])).
% 3.34/1.49  tff(c_332, plain, (![B_145, D_146, F_147]: (k1_funct_1(k8_funct_2(B_145, '#skF_1', '#skF_3', D_146, '#skF_5'), F_147)=k1_funct_1('#skF_5', k1_funct_1(D_146, F_147)) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(B_145, '#skF_1', D_146), '#skF_1') | ~m1_subset_1(F_147, B_145) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(B_145, '#skF_1'))) | ~v1_funct_2(D_146, B_145, '#skF_1') | ~v1_funct_1(D_146) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_323])).
% 3.34/1.49  tff(c_395, plain, (![B_159, D_160, F_161]: (k1_funct_1(k8_funct_2(B_159, '#skF_1', '#skF_3', D_160, '#skF_5'), F_161)=k1_funct_1('#skF_5', k1_funct_1(D_160, F_161)) | k1_xboole_0=B_159 | ~r1_tarski(k2_relset_1(B_159, '#skF_1', D_160), '#skF_1') | ~m1_subset_1(F_161, B_159) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_1'))) | ~v1_funct_2(D_160, B_159, '#skF_1') | ~v1_funct_1(D_160))), inference(negUnitSimplification, [status(thm)], [c_52, c_332])).
% 3.34/1.49  tff(c_400, plain, (![F_161]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_161)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_161)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_161, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_395])).
% 3.34/1.49  tff(c_404, plain, (![F_161]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_161)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_161)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_161, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_112, c_400])).
% 3.34/1.49  tff(c_405, plain, (![F_161]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_161)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_161)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_161, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_371, c_404])).
% 3.34/1.49  tff(c_406, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_405])).
% 3.34/1.49  tff(c_409, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_406])).
% 3.34/1.49  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_89, c_409])).
% 3.34/1.49  tff(c_414, plain, (![F_161]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_161)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_161)) | ~m1_subset_1(F_161, '#skF_2'))), inference(splitRight, [status(thm)], [c_405])).
% 3.34/1.49  tff(c_162, plain, (![B_103, C_101, A_104, D_105, E_102]: (v1_funct_1(k8_funct_2(A_104, B_103, C_101, D_105, E_102)) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(B_103, C_101))) | ~v1_funct_1(E_102) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_2(D_105, A_104, B_103) | ~v1_funct_1(D_105))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.49  tff(c_166, plain, (![A_104, D_105]: (v1_funct_1(k8_funct_2(A_104, '#skF_1', '#skF_3', D_105, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_104, '#skF_1'))) | ~v1_funct_2(D_105, A_104, '#skF_1') | ~v1_funct_1(D_105))), inference(resolution, [status(thm)], [c_40, c_162])).
% 3.34/1.49  tff(c_174, plain, (![A_108, D_109]: (v1_funct_1(k8_funct_2(A_108, '#skF_1', '#skF_3', D_109, '#skF_5')) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_108, '#skF_1'))) | ~v1_funct_2(D_109, A_108, '#skF_1') | ~v1_funct_1(D_109))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_166])).
% 3.34/1.49  tff(c_177, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_174])).
% 3.34/1.49  tff(c_180, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_177])).
% 3.34/1.49  tff(c_193, plain, (![D_116, B_114, A_115, C_112, E_113]: (v1_funct_2(k8_funct_2(A_115, B_114, C_112, D_116, E_113), A_115, C_112) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(B_114, C_112))) | ~v1_funct_1(E_113) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_2(D_116, A_115, B_114) | ~v1_funct_1(D_116))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.49  tff(c_197, plain, (![A_115, D_116]: (v1_funct_2(k8_funct_2(A_115, '#skF_1', '#skF_3', D_116, '#skF_5'), A_115, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_115, '#skF_1'))) | ~v1_funct_2(D_116, A_115, '#skF_1') | ~v1_funct_1(D_116))), inference(resolution, [status(thm)], [c_40, c_193])).
% 3.34/1.49  tff(c_205, plain, (![A_119, D_120]: (v1_funct_2(k8_funct_2(A_119, '#skF_1', '#skF_3', D_120, '#skF_5'), A_119, '#skF_3') | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(A_119, '#skF_1'))) | ~v1_funct_2(D_120, A_119, '#skF_1') | ~v1_funct_1(D_120))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_197])).
% 3.34/1.49  tff(c_207, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_205])).
% 3.34/1.49  tff(c_210, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_207])).
% 3.34/1.49  tff(c_24, plain, (![A_19, C_21, D_22, B_20, E_23]: (m1_subset_1(k8_funct_2(A_19, B_20, C_21, D_22, E_23), k1_zfmisc_1(k2_zfmisc_1(A_19, C_21))) | ~m1_subset_1(E_23, k1_zfmisc_1(k2_zfmisc_1(B_20, C_21))) | ~v1_funct_1(E_23) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(D_22, A_19, B_20) | ~v1_funct_1(D_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.49  tff(c_211, plain, (![C_121, A_124, E_122, D_125, B_123]: (m1_subset_1(k8_funct_2(A_124, B_123, C_121, D_125, E_122), k1_zfmisc_1(k2_zfmisc_1(A_124, C_121))) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(B_123, C_121))) | ~v1_funct_1(E_122) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(D_125, A_124, B_123) | ~v1_funct_1(D_125))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.49  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.49  tff(c_442, plain, (![C_169, E_166, A_167, D_168, B_170]: (k1_relset_1(A_167, C_169, k8_funct_2(A_167, B_170, C_169, D_168, E_166))=k1_relat_1(k8_funct_2(A_167, B_170, C_169, D_168, E_166)) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(B_170, C_169))) | ~v1_funct_1(E_166) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(A_167, B_170))) | ~v1_funct_2(D_168, A_167, B_170) | ~v1_funct_1(D_168))), inference(resolution, [status(thm)], [c_211, c_16])).
% 3.34/1.49  tff(c_448, plain, (![A_167, D_168]: (k1_relset_1(A_167, '#skF_3', k8_funct_2(A_167, '#skF_1', '#skF_3', D_168, '#skF_5'))=k1_relat_1(k8_funct_2(A_167, '#skF_1', '#skF_3', D_168, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(A_167, '#skF_1'))) | ~v1_funct_2(D_168, A_167, '#skF_1') | ~v1_funct_1(D_168))), inference(resolution, [status(thm)], [c_40, c_442])).
% 3.34/1.49  tff(c_461, plain, (![A_173, D_174]: (k1_relset_1(A_173, '#skF_3', k8_funct_2(A_173, '#skF_1', '#skF_3', D_174, '#skF_5'))=k1_relat_1(k8_funct_2(A_173, '#skF_1', '#skF_3', D_174, '#skF_5')) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_173, '#skF_1'))) | ~v1_funct_2(D_174, A_173, '#skF_1') | ~v1_funct_1(D_174))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_448])).
% 3.34/1.49  tff(c_466, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_461])).
% 3.34/1.49  tff(c_470, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_466])).
% 3.34/1.49  tff(c_32, plain, (![C_30, F_44, D_38, B_29, E_42, A_28]: (k1_funct_1(k8_funct_2(B_29, C_30, A_28, D_38, E_42), F_44)=k1_funct_1(E_42, k1_funct_1(D_38, F_44)) | k1_xboole_0=B_29 | ~r1_tarski(k2_relset_1(B_29, C_30, D_38), k1_relset_1(C_30, A_28, E_42)) | ~m1_subset_1(F_44, B_29) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(C_30, A_28))) | ~v1_funct_1(E_42) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_29, C_30))) | ~v1_funct_2(D_38, B_29, C_30) | ~v1_funct_1(D_38) | v1_xboole_0(C_30))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.34/1.49  tff(c_473, plain, (![B_29, D_38, F_44]: (k1_funct_1(k8_funct_2(B_29, '#skF_2', '#skF_3', D_38, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_44)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_38, F_44)) | k1_xboole_0=B_29 | ~r1_tarski(k2_relset_1(B_29, '#skF_2', D_38), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_44, B_29) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_29, '#skF_2'))) | ~v1_funct_2(D_38, B_29, '#skF_2') | ~v1_funct_1(D_38) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_32])).
% 3.34/1.49  tff(c_477, plain, (![B_29, D_38, F_44]: (k1_funct_1(k8_funct_2(B_29, '#skF_2', '#skF_3', D_38, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_44)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_38, F_44)) | k1_xboole_0=B_29 | ~r1_tarski(k2_relset_1(B_29, '#skF_2', D_38), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_44, B_29) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_29, '#skF_2'))) | ~v1_funct_2(D_38, B_29, '#skF_2') | ~v1_funct_1(D_38) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_473])).
% 3.34/1.49  tff(c_478, plain, (![B_29, D_38, F_44]: (k1_funct_1(k8_funct_2(B_29, '#skF_2', '#skF_3', D_38, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_44)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_38, F_44)) | k1_xboole_0=B_29 | ~r1_tarski(k2_relset_1(B_29, '#skF_2', D_38), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_44, B_29) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_29, '#skF_2'))) | ~v1_funct_2(D_38, B_29, '#skF_2') | ~v1_funct_1(D_38))), inference(negUnitSimplification, [status(thm)], [c_50, c_477])).
% 3.34/1.49  tff(c_558, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_478])).
% 3.34/1.49  tff(c_561, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_558])).
% 3.34/1.49  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_561])).
% 3.34/1.49  tff(c_567, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_478])).
% 3.34/1.49  tff(c_150, plain, (![A_97, B_98, C_99, D_100]: (k3_funct_2(A_97, B_98, C_99, D_100)=k1_funct_1(C_99, D_100) | ~m1_subset_1(D_100, A_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(C_99, A_97, B_98) | ~v1_funct_1(C_99) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.34/1.49  tff(c_156, plain, (![B_98, C_99]: (k3_funct_2('#skF_2', B_98, C_99, '#skF_6')=k1_funct_1(C_99, '#skF_6') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_98))) | ~v1_funct_2(C_99, '#skF_2', B_98) | ~v1_funct_1(C_99) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_150])).
% 3.34/1.49  tff(c_161, plain, (![B_98, C_99]: (k3_funct_2('#skF_2', B_98, C_99, '#skF_6')=k1_funct_1(C_99, '#skF_6') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_98))) | ~v1_funct_2(C_99, '#skF_2', B_98) | ~v1_funct_1(C_99))), inference(negUnitSimplification, [status(thm)], [c_50, c_156])).
% 3.34/1.49  tff(c_586, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_567, c_161])).
% 3.34/1.49  tff(c_632, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_210, c_586])).
% 3.34/1.49  tff(c_181, plain, (![B_110, C_111]: (k3_funct_2('#skF_2', B_110, C_111, '#skF_6')=k1_funct_1(C_111, '#skF_6') | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_110))) | ~v1_funct_2(C_111, '#skF_2', B_110) | ~v1_funct_1(C_111))), inference(negUnitSimplification, [status(thm)], [c_50, c_156])).
% 3.34/1.49  tff(c_184, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_181])).
% 3.34/1.49  tff(c_187, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_184])).
% 3.34/1.49  tff(c_34, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.34/1.49  tff(c_188, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_34])).
% 3.34/1.49  tff(c_648, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_632, c_188])).
% 3.34/1.49  tff(c_655, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_414, c_648])).
% 3.34/1.49  tff(c_659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_655])).
% 3.34/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.49  
% 3.34/1.49  Inference rules
% 3.34/1.49  ----------------------
% 3.34/1.49  #Ref     : 0
% 3.34/1.49  #Sup     : 126
% 3.34/1.49  #Fact    : 0
% 3.34/1.49  #Define  : 0
% 3.34/1.49  #Split   : 8
% 3.34/1.49  #Chain   : 0
% 3.34/1.49  #Close   : 0
% 3.34/1.49  
% 3.34/1.49  Ordering : KBO
% 3.34/1.49  
% 3.34/1.49  Simplification rules
% 3.34/1.49  ----------------------
% 3.34/1.49  #Subsume      : 2
% 3.34/1.49  #Demod        : 101
% 3.34/1.49  #Tautology    : 28
% 3.34/1.49  #SimpNegUnit  : 8
% 3.34/1.49  #BackRed      : 4
% 3.34/1.49  
% 3.34/1.49  #Partial instantiations: 0
% 3.34/1.49  #Strategies tried      : 1
% 3.34/1.49  
% 3.34/1.49  Timing (in seconds)
% 3.34/1.49  ----------------------
% 3.49/1.49  Preprocessing        : 0.33
% 3.49/1.49  Parsing              : 0.18
% 3.49/1.50  CNF conversion       : 0.03
% 3.49/1.50  Main loop            : 0.39
% 3.49/1.50  Inferencing          : 0.13
% 3.49/1.50  Reduction            : 0.13
% 3.49/1.50  Demodulation         : 0.09
% 3.49/1.50  BG Simplification    : 0.02
% 3.49/1.50  Subsumption          : 0.07
% 3.49/1.50  Abstraction          : 0.02
% 3.49/1.50  MUC search           : 0.00
% 3.49/1.50  Cooper               : 0.00
% 3.49/1.50  Total                : 0.77
% 3.49/1.50  Index Insertion      : 0.00
% 3.49/1.50  Index Deletion       : 0.00
% 3.49/1.50  Index Matching       : 0.00
% 3.49/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
