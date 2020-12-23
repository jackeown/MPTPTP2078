%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:54 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 242 expanded)
%              Number of leaves         :   43 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 427 expanded)
%              Number of equality atoms :   62 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_86,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1439,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( k8_relset_1(A_204,B_205,C_206,D_207) = k10_relat_1(C_206,D_207)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1442,plain,(
    ! [D_207] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_207) = k10_relat_1('#skF_3',D_207) ),
    inference(resolution,[status(thm)],[c_48,c_1439])).

tff(c_1190,plain,(
    ! [A_181,B_182,C_183] :
      ( k1_relset_1(A_181,B_182,C_183) = k1_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1194,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1190])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_134,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_138,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_141,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_18])).

tff(c_144,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_141])).

tff(c_173,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(k7_relat_1(B_73,A_74)) = k9_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_173])).

tff(c_198,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_191])).

tff(c_888,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k7_relset_1(A_131,B_132,C_133,D_134) = k9_relat_1(C_133,D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_891,plain,(
    ! [D_134] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_134) = k9_relat_1('#skF_3',D_134) ),
    inference(resolution,[status(thm)],[c_48,c_888])).

tff(c_697,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_701,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_697])).

tff(c_46,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_78,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_702,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_78])).

tff(c_892,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_702])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_892])).

tff(c_896,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1195,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_896])).

tff(c_1443,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_1195])).

tff(c_1010,plain,(
    ! [C_155,B_156,A_157] :
      ( v5_relat_1(C_155,B_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1014,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1010])).

tff(c_957,plain,(
    ! [C_146,A_147,B_148] :
      ( v4_relat_1(C_146,A_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_961,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_957])).

tff(c_964,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_961,c_18])).

tff(c_967,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_964])).

tff(c_1015,plain,(
    ! [B_158,A_159] :
      ( k2_relat_1(k7_relat_1(B_158,A_159)) = k9_relat_1(B_158,A_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1036,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1015])).

tff(c_1043,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1036])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1592,plain,(
    ! [B_218,A_219,A_220] :
      ( r1_tarski(k9_relat_1(B_218,A_219),A_220)
      | ~ v5_relat_1(k7_relat_1(B_218,A_219),A_220)
      | ~ v1_relat_1(k7_relat_1(B_218,A_219))
      | ~ v1_relat_1(B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_6])).

tff(c_1602,plain,(
    ! [A_220] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_220)
      | ~ v5_relat_1('#skF_3',A_220)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1592])).

tff(c_1613,plain,(
    ! [A_221] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_221)
      | ~ v5_relat_1('#skF_3',A_221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_967,c_1043,c_1602])).

tff(c_26,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [B_25,A_24] : k5_relat_1(k6_relat_1(B_25),k6_relat_1(A_24)) = k6_relat_1(k3_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1214,plain,(
    ! [B_187,A_188] :
      ( k9_relat_1(B_187,k2_relat_1(A_188)) = k2_relat_1(k5_relat_1(A_188,B_187))
      | ~ v1_relat_1(B_187)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1242,plain,(
    ! [A_22,B_187] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_22),B_187)) = k9_relat_1(B_187,A_22)
      | ~ v1_relat_1(B_187)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1214])).

tff(c_1276,plain,(
    ! [A_194,B_195] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_194),B_195)) = k9_relat_1(B_195,A_194)
      | ~ v1_relat_1(B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1242])).

tff(c_1303,plain,(
    ! [A_24,B_25] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_24,B_25))) = k9_relat_1(k6_relat_1(A_24),B_25)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1276])).

tff(c_1307,plain,(
    ! [A_24,B_25] : k9_relat_1(k6_relat_1(A_24),B_25) = k3_xboole_0(A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1303])).

tff(c_28,plain,(
    ! [A_23] : v4_relat_1(k6_relat_1(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1059,plain,(
    ! [C_161,B_162,A_163] :
      ( v4_relat_1(C_161,B_162)
      | ~ v4_relat_1(C_161,A_163)
      | ~ v1_relat_1(C_161)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1063,plain,(
    ! [A_23,B_162] :
      ( v4_relat_1(k6_relat_1(A_23),B_162)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_23,B_162) ) ),
    inference(resolution,[status(thm)],[c_28,c_1059])).

tff(c_1082,plain,(
    ! [A_165,B_166] :
      ( v4_relat_1(k6_relat_1(A_165),B_166)
      | ~ r1_tarski(A_165,B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1063])).

tff(c_1087,plain,(
    ! [A_165,B_166] :
      ( k7_relat_1(k6_relat_1(A_165),B_166) = k6_relat_1(A_165)
      | ~ v1_relat_1(k6_relat_1(A_165))
      | ~ r1_tarski(A_165,B_166) ) ),
    inference(resolution,[status(thm)],[c_1082,c_18])).

tff(c_1101,plain,(
    ! [A_168,B_169] :
      ( k7_relat_1(k6_relat_1(A_168),B_169) = k6_relat_1(A_168)
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1087])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1107,plain,(
    ! [A_168,B_169] :
      ( k9_relat_1(k6_relat_1(A_168),B_169) = k2_relat_1(k6_relat_1(A_168))
      | ~ v1_relat_1(k6_relat_1(A_168))
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_10])).

tff(c_1120,plain,(
    ! [A_168,B_169] :
      ( k9_relat_1(k6_relat_1(A_168),B_169) = A_168
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1107])).

tff(c_1308,plain,(
    ! [A_168,B_169] :
      ( k3_xboole_0(A_168,B_169) = A_168
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_1120])).

tff(c_1647,plain,(
    ! [A_224] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_224) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_224) ) ),
    inference(resolution,[status(thm)],[c_1613,c_1308])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k10_relat_1(B_14,k3_xboole_0(k2_relat_1(B_14),A_13)) = k10_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1663,plain,(
    ! [A_224] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_224)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_14])).

tff(c_1751,plain,(
    ! [A_228] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_228)
      | ~ v5_relat_1('#skF_3',A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1663])).

tff(c_1757,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1014,c_1751])).

tff(c_16,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1766,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_16])).

tff(c_1773,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1766])).

tff(c_1775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1443,c_1773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  
% 3.64/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.64/1.64  
% 3.64/1.64  %Foreground sorts:
% 3.64/1.64  
% 3.64/1.64  
% 3.64/1.64  %Background operators:
% 3.64/1.64  
% 3.64/1.64  
% 3.64/1.64  %Foreground operators:
% 3.64/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.64/1.64  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.64/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.64/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.64/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.64/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.64/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.64/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.64  
% 3.64/1.65  tff(f_115, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.64/1.65  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.64/1.65  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.64/1.65  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.64/1.65  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.65  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.65  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.64/1.65  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.64/1.65  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.64/1.65  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.64/1.65  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.64/1.65  tff(f_84, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.64/1.65  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.64/1.65  tff(f_86, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.64/1.65  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.64/1.65  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 3.64/1.65  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.64/1.65  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.64/1.65  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.65  tff(c_1439, plain, (![A_204, B_205, C_206, D_207]: (k8_relset_1(A_204, B_205, C_206, D_207)=k10_relat_1(C_206, D_207) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.65  tff(c_1442, plain, (![D_207]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_207)=k10_relat_1('#skF_3', D_207))), inference(resolution, [status(thm)], [c_48, c_1439])).
% 3.64/1.65  tff(c_1190, plain, (![A_181, B_182, C_183]: (k1_relset_1(A_181, B_182, C_183)=k1_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.65  tff(c_1194, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1190])).
% 3.64/1.65  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.64/1.65  tff(c_71, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.65  tff(c_74, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 3.64/1.65  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_74])).
% 3.64/1.65  tff(c_134, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.64/1.65  tff(c_138, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_134])).
% 3.64/1.65  tff(c_18, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.65  tff(c_141, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_18])).
% 3.64/1.65  tff(c_144, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_141])).
% 3.64/1.65  tff(c_173, plain, (![B_73, A_74]: (k2_relat_1(k7_relat_1(B_73, A_74))=k9_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.65  tff(c_191, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_173])).
% 3.64/1.65  tff(c_198, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_191])).
% 3.64/1.65  tff(c_888, plain, (![A_131, B_132, C_133, D_134]: (k7_relset_1(A_131, B_132, C_133, D_134)=k9_relat_1(C_133, D_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.64/1.66  tff(c_891, plain, (![D_134]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_134)=k9_relat_1('#skF_3', D_134))), inference(resolution, [status(thm)], [c_48, c_888])).
% 3.64/1.66  tff(c_697, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.64/1.66  tff(c_701, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_697])).
% 3.64/1.66  tff(c_46, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.66  tff(c_78, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.64/1.66  tff(c_702, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_701, c_78])).
% 3.64/1.66  tff(c_892, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_891, c_702])).
% 3.64/1.66  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_892])).
% 3.64/1.66  tff(c_896, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.64/1.66  tff(c_1195, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_896])).
% 3.64/1.66  tff(c_1443, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_1195])).
% 3.64/1.66  tff(c_1010, plain, (![C_155, B_156, A_157]: (v5_relat_1(C_155, B_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.64/1.66  tff(c_1014, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_1010])).
% 3.64/1.66  tff(c_957, plain, (![C_146, A_147, B_148]: (v4_relat_1(C_146, A_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.64/1.66  tff(c_961, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_957])).
% 3.64/1.66  tff(c_964, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_961, c_18])).
% 3.64/1.66  tff(c_967, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_964])).
% 3.64/1.66  tff(c_1015, plain, (![B_158, A_159]: (k2_relat_1(k7_relat_1(B_158, A_159))=k9_relat_1(B_158, A_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.66  tff(c_1036, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_967, c_1015])).
% 3.64/1.66  tff(c_1043, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1036])).
% 3.64/1.66  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.64/1.66  tff(c_1592, plain, (![B_218, A_219, A_220]: (r1_tarski(k9_relat_1(B_218, A_219), A_220) | ~v5_relat_1(k7_relat_1(B_218, A_219), A_220) | ~v1_relat_1(k7_relat_1(B_218, A_219)) | ~v1_relat_1(B_218))), inference(superposition, [status(thm), theory('equality')], [c_1015, c_6])).
% 3.64/1.66  tff(c_1602, plain, (![A_220]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_220) | ~v5_relat_1('#skF_3', A_220) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_967, c_1592])).
% 3.64/1.66  tff(c_1613, plain, (![A_221]: (r1_tarski(k2_relat_1('#skF_3'), A_221) | ~v5_relat_1('#skF_3', A_221))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_967, c_1043, c_1602])).
% 3.64/1.66  tff(c_26, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.64/1.66  tff(c_24, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.64/1.66  tff(c_32, plain, (![B_25, A_24]: (k5_relat_1(k6_relat_1(B_25), k6_relat_1(A_24))=k6_relat_1(k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.64/1.66  tff(c_1214, plain, (![B_187, A_188]: (k9_relat_1(B_187, k2_relat_1(A_188))=k2_relat_1(k5_relat_1(A_188, B_187)) | ~v1_relat_1(B_187) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.64/1.66  tff(c_1242, plain, (![A_22, B_187]: (k2_relat_1(k5_relat_1(k6_relat_1(A_22), B_187))=k9_relat_1(B_187, A_22) | ~v1_relat_1(B_187) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1214])).
% 3.64/1.66  tff(c_1276, plain, (![A_194, B_195]: (k2_relat_1(k5_relat_1(k6_relat_1(A_194), B_195))=k9_relat_1(B_195, A_194) | ~v1_relat_1(B_195))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1242])).
% 3.64/1.66  tff(c_1303, plain, (![A_24, B_25]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_24, B_25)))=k9_relat_1(k6_relat_1(A_24), B_25) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1276])).
% 3.64/1.66  tff(c_1307, plain, (![A_24, B_25]: (k9_relat_1(k6_relat_1(A_24), B_25)=k3_xboole_0(A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1303])).
% 3.64/1.66  tff(c_28, plain, (![A_23]: (v4_relat_1(k6_relat_1(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.64/1.66  tff(c_1059, plain, (![C_161, B_162, A_163]: (v4_relat_1(C_161, B_162) | ~v4_relat_1(C_161, A_163) | ~v1_relat_1(C_161) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.64/1.66  tff(c_1063, plain, (![A_23, B_162]: (v4_relat_1(k6_relat_1(A_23), B_162) | ~v1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_23, B_162))), inference(resolution, [status(thm)], [c_28, c_1059])).
% 3.64/1.66  tff(c_1082, plain, (![A_165, B_166]: (v4_relat_1(k6_relat_1(A_165), B_166) | ~r1_tarski(A_165, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1063])).
% 3.64/1.66  tff(c_1087, plain, (![A_165, B_166]: (k7_relat_1(k6_relat_1(A_165), B_166)=k6_relat_1(A_165) | ~v1_relat_1(k6_relat_1(A_165)) | ~r1_tarski(A_165, B_166))), inference(resolution, [status(thm)], [c_1082, c_18])).
% 3.64/1.66  tff(c_1101, plain, (![A_168, B_169]: (k7_relat_1(k6_relat_1(A_168), B_169)=k6_relat_1(A_168) | ~r1_tarski(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1087])).
% 3.64/1.66  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.64/1.66  tff(c_1107, plain, (![A_168, B_169]: (k9_relat_1(k6_relat_1(A_168), B_169)=k2_relat_1(k6_relat_1(A_168)) | ~v1_relat_1(k6_relat_1(A_168)) | ~r1_tarski(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_10])).
% 3.64/1.66  tff(c_1120, plain, (![A_168, B_169]: (k9_relat_1(k6_relat_1(A_168), B_169)=A_168 | ~r1_tarski(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1107])).
% 3.64/1.66  tff(c_1308, plain, (![A_168, B_169]: (k3_xboole_0(A_168, B_169)=A_168 | ~r1_tarski(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_1120])).
% 3.64/1.66  tff(c_1647, plain, (![A_224]: (k3_xboole_0(k2_relat_1('#skF_3'), A_224)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_224))), inference(resolution, [status(thm)], [c_1613, c_1308])).
% 3.64/1.66  tff(c_14, plain, (![B_14, A_13]: (k10_relat_1(B_14, k3_xboole_0(k2_relat_1(B_14), A_13))=k10_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.64/1.66  tff(c_1663, plain, (![A_224]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_224) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_224))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_14])).
% 3.64/1.66  tff(c_1751, plain, (![A_228]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_228) | ~v5_relat_1('#skF_3', A_228))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1663])).
% 3.64/1.66  tff(c_1757, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1014, c_1751])).
% 3.64/1.66  tff(c_16, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.64/1.66  tff(c_1766, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1757, c_16])).
% 3.64/1.66  tff(c_1773, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1766])).
% 3.64/1.66  tff(c_1775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1443, c_1773])).
% 3.64/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.66  
% 3.64/1.66  Inference rules
% 3.64/1.66  ----------------------
% 3.64/1.66  #Ref     : 0
% 3.64/1.66  #Sup     : 390
% 3.64/1.66  #Fact    : 0
% 3.64/1.66  #Define  : 0
% 3.64/1.66  #Split   : 3
% 3.64/1.66  #Chain   : 0
% 3.64/1.66  #Close   : 0
% 3.64/1.66  
% 3.64/1.66  Ordering : KBO
% 3.64/1.66  
% 3.64/1.66  Simplification rules
% 3.64/1.66  ----------------------
% 3.64/1.66  #Subsume      : 26
% 3.64/1.66  #Demod        : 256
% 3.64/1.66  #Tautology    : 175
% 3.64/1.66  #SimpNegUnit  : 1
% 3.64/1.66  #BackRed      : 8
% 3.64/1.66  
% 3.64/1.66  #Partial instantiations: 0
% 3.64/1.66  #Strategies tried      : 1
% 3.64/1.66  
% 3.64/1.66  Timing (in seconds)
% 3.64/1.66  ----------------------
% 3.64/1.66  Preprocessing        : 0.34
% 3.64/1.66  Parsing              : 0.20
% 3.64/1.66  CNF conversion       : 0.02
% 3.64/1.66  Main loop            : 0.51
% 3.64/1.66  Inferencing          : 0.20
% 3.64/1.66  Reduction            : 0.17
% 3.64/1.66  Demodulation         : 0.12
% 3.64/1.66  BG Simplification    : 0.03
% 3.64/1.66  Subsumption          : 0.08
% 3.64/1.66  Abstraction          : 0.03
% 3.64/1.66  MUC search           : 0.00
% 3.64/1.66  Cooper               : 0.00
% 3.64/1.66  Total                : 0.89
% 3.64/1.66  Index Insertion      : 0.00
% 3.64/1.66  Index Deletion       : 0.00
% 3.64/1.66  Index Matching       : 0.00
% 3.64/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
