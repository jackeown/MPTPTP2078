%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:59 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 194 expanded)
%              Number of leaves         :   42 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 333 expanded)
%              Number of equality atoms :   68 ( 117 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_877,plain,(
    ! [B_129,A_130] :
      ( v1_relat_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_130))
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_880,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_877])).

tff(c_883,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_880])).

tff(c_24,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1573,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k8_relset_1(A_196,B_197,C_198,D_199) = k10_relat_1(C_198,D_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1576,plain,(
    ! [D_199] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_199) = k10_relat_1('#skF_3',D_199) ),
    inference(resolution,[status(thm)],[c_52,c_1573])).

tff(c_893,plain,(
    ! [C_134,A_135,B_136] :
      ( v4_relat_1(C_134,A_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_897,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_893])).

tff(c_968,plain,(
    ! [B_149,A_150] :
      ( k7_relat_1(B_149,A_150) = B_149
      | ~ v4_relat_1(B_149,A_150)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_971,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_897,c_968])).

tff(c_974,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_971])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_978,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_22])).

tff(c_982,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_978])).

tff(c_1389,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k7_relset_1(A_184,B_185,C_186,D_187) = k9_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1392,plain,(
    ! [D_187] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_187) = k9_relat_1('#skF_3',D_187) ),
    inference(resolution,[status(thm)],[c_52,c_1389])).

tff(c_106,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_109,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_106])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_109])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [B_59,A_60] :
      ( v4_relat_1(B_59,A_60)
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_149,plain,(
    ! [B_61] :
      ( v4_relat_1(B_61,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_197,plain,(
    ! [B_69] :
      ( k7_relat_1(B_69,k1_relat_1(B_69)) = B_69
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_149,c_28])).

tff(c_203,plain,(
    ! [B_69] :
      ( k9_relat_1(B_69,k1_relat_1(B_69)) = k2_relat_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_22])).

tff(c_214,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_218,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_214])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_301,plain,(
    ! [B_84,A_85] :
      ( k5_relat_1(B_84,k6_relat_1(A_85)) = B_84
      | ~ r1_tarski(k2_relat_1(B_84),A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_315,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = B_9
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_301])).

tff(c_18,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_515,plain,(
    ! [A_101,B_102] :
      ( k10_relat_1(A_101,k1_relat_1(B_102)) = k1_relat_1(k5_relat_1(A_101,B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_532,plain,(
    ! [A_101,A_21] :
      ( k1_relat_1(k5_relat_1(A_101,k6_relat_1(A_21))) = k10_relat_1(A_101,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_515])).

tff(c_541,plain,(
    ! [A_103,A_104] :
      ( k1_relat_1(k5_relat_1(A_103,k6_relat_1(A_104))) = k10_relat_1(A_103,A_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_532])).

tff(c_840,plain,(
    ! [B_127,A_128] :
      ( k10_relat_1(B_127,A_128) = k1_relat_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v5_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_541])).

tff(c_852,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_840])).

tff(c_862,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_852])).

tff(c_826,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k7_relset_1(A_122,B_123,C_124,D_125) = k9_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_829,plain,(
    ! [D_125] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_125) = k9_relat_1('#skF_3',D_125) ),
    inference(resolution,[status(thm)],[c_52,c_826])).

tff(c_793,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k8_relset_1(A_115,B_116,C_117,D_118) = k10_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_796,plain,(
    ! [D_118] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_118) = k10_relat_1('#skF_3',D_118) ),
    inference(resolution,[status(thm)],[c_52,c_793])).

tff(c_362,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_366,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_362])).

tff(c_50,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_105,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_367,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_105])).

tff(c_797,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_367])).

tff(c_830,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_797])).

tff(c_863,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_830])).

tff(c_870,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_863])).

tff(c_874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_870])).

tff(c_875,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1393,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_875])).

tff(c_1394,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_1393])).

tff(c_1577,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_1394])).

tff(c_1595,plain,
    ( k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1577])).

tff(c_1597,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_1595])).

tff(c_884,plain,(
    ! [C_131,B_132,A_133] :
      ( v5_relat_1(C_131,B_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_888,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_884])).

tff(c_1056,plain,(
    ! [B_160,A_161] :
      ( k5_relat_1(B_160,k6_relat_1(A_161)) = B_160
      | ~ r1_tarski(k2_relat_1(B_160),A_161)
      | ~ v1_relat_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1070,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = B_9
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_1056])).

tff(c_1320,plain,(
    ! [A_180,B_181] :
      ( k10_relat_1(A_180,k1_relat_1(B_181)) = k1_relat_1(k5_relat_1(A_180,B_181))
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1337,plain,(
    ! [A_180,A_21] :
      ( k1_relat_1(k5_relat_1(A_180,k6_relat_1(A_21))) = k10_relat_1(A_180,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1320])).

tff(c_1346,plain,(
    ! [A_182,A_183] :
      ( k1_relat_1(k5_relat_1(A_182,k6_relat_1(A_183))) = k10_relat_1(A_182,A_183)
      | ~ v1_relat_1(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1337])).

tff(c_1654,plain,(
    ! [B_205,A_206] :
      ( k10_relat_1(B_205,A_206) = k1_relat_1(B_205)
      | ~ v1_relat_1(B_205)
      | ~ v5_relat_1(B_205,A_206)
      | ~ v1_relat_1(B_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_1346])).

tff(c_1666,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_888,c_1654])).

tff(c_1676,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_1666])).

tff(c_1683,plain,(
    ! [A_207,B_208,C_209] :
      ( k8_relset_1(A_207,B_208,C_209,B_208) = k1_relset_1(A_207,B_208,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1685,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1683])).

tff(c_1687,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1576,c_1685])).

tff(c_1689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1597,c_1687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.61  
% 3.27/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.61  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.27/1.61  
% 3.27/1.61  %Foreground sorts:
% 3.27/1.61  
% 3.27/1.61  
% 3.27/1.61  %Background operators:
% 3.27/1.61  
% 3.27/1.61  
% 3.27/1.61  %Foreground operators:
% 3.27/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.27/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.27/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.27/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.27/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.27/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.27/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.61  
% 3.66/1.63  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.66/1.63  tff(f_116, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.66/1.63  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.66/1.63  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.66/1.63  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.66/1.63  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.66/1.63  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.66/1.63  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.66/1.63  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.66/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.66/1.63  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.66/1.63  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.66/1.63  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.66/1.63  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.66/1.63  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.66/1.63  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.66/1.63  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.66/1.63  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.66/1.63  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.66/1.63  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.66/1.63  tff(c_877, plain, (![B_129, A_130]: (v1_relat_1(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_130)) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.63  tff(c_880, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_877])).
% 3.66/1.63  tff(c_883, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_880])).
% 3.66/1.63  tff(c_24, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.66/1.63  tff(c_1573, plain, (![A_196, B_197, C_198, D_199]: (k8_relset_1(A_196, B_197, C_198, D_199)=k10_relat_1(C_198, D_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.66/1.63  tff(c_1576, plain, (![D_199]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_199)=k10_relat_1('#skF_3', D_199))), inference(resolution, [status(thm)], [c_52, c_1573])).
% 3.66/1.63  tff(c_893, plain, (![C_134, A_135, B_136]: (v4_relat_1(C_134, A_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.66/1.63  tff(c_897, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_893])).
% 3.66/1.63  tff(c_968, plain, (![B_149, A_150]: (k7_relat_1(B_149, A_150)=B_149 | ~v4_relat_1(B_149, A_150) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.66/1.63  tff(c_971, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_897, c_968])).
% 3.66/1.63  tff(c_974, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_883, c_971])).
% 3.66/1.63  tff(c_22, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.66/1.63  tff(c_978, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_974, c_22])).
% 3.66/1.63  tff(c_982, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_978])).
% 3.66/1.63  tff(c_1389, plain, (![A_184, B_185, C_186, D_187]: (k7_relset_1(A_184, B_185, C_186, D_187)=k9_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.66/1.63  tff(c_1392, plain, (![D_187]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_187)=k9_relat_1('#skF_3', D_187))), inference(resolution, [status(thm)], [c_52, c_1389])).
% 3.66/1.63  tff(c_106, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.66/1.63  tff(c_109, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_106])).
% 3.66/1.63  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_109])).
% 3.66/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.63  tff(c_138, plain, (![B_59, A_60]: (v4_relat_1(B_59, A_60) | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.63  tff(c_149, plain, (![B_61]: (v4_relat_1(B_61, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_6, c_138])).
% 3.66/1.63  tff(c_28, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.66/1.63  tff(c_197, plain, (![B_69]: (k7_relat_1(B_69, k1_relat_1(B_69))=B_69 | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_149, c_28])).
% 3.66/1.63  tff(c_203, plain, (![B_69]: (k9_relat_1(B_69, k1_relat_1(B_69))=k2_relat_1(B_69) | ~v1_relat_1(B_69) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_197, c_22])).
% 3.66/1.63  tff(c_214, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.66/1.63  tff(c_218, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_214])).
% 3.66/1.63  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.66/1.63  tff(c_301, plain, (![B_84, A_85]: (k5_relat_1(B_84, k6_relat_1(A_85))=B_84 | ~r1_tarski(k2_relat_1(B_84), A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.63  tff(c_315, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=B_9 | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_16, c_301])).
% 3.66/1.63  tff(c_18, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.66/1.63  tff(c_30, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.66/1.63  tff(c_515, plain, (![A_101, B_102]: (k10_relat_1(A_101, k1_relat_1(B_102))=k1_relat_1(k5_relat_1(A_101, B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.66/1.63  tff(c_532, plain, (![A_101, A_21]: (k1_relat_1(k5_relat_1(A_101, k6_relat_1(A_21)))=k10_relat_1(A_101, A_21) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_30, c_515])).
% 3.66/1.63  tff(c_541, plain, (![A_103, A_104]: (k1_relat_1(k5_relat_1(A_103, k6_relat_1(A_104)))=k10_relat_1(A_103, A_104) | ~v1_relat_1(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_532])).
% 3.66/1.63  tff(c_840, plain, (![B_127, A_128]: (k10_relat_1(B_127, A_128)=k1_relat_1(B_127) | ~v1_relat_1(B_127) | ~v5_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(superposition, [status(thm), theory('equality')], [c_315, c_541])).
% 3.66/1.63  tff(c_852, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_218, c_840])).
% 3.66/1.63  tff(c_862, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_852])).
% 3.66/1.63  tff(c_826, plain, (![A_122, B_123, C_124, D_125]: (k7_relset_1(A_122, B_123, C_124, D_125)=k9_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.66/1.63  tff(c_829, plain, (![D_125]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_125)=k9_relat_1('#skF_3', D_125))), inference(resolution, [status(thm)], [c_52, c_826])).
% 3.66/1.63  tff(c_793, plain, (![A_115, B_116, C_117, D_118]: (k8_relset_1(A_115, B_116, C_117, D_118)=k10_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.66/1.63  tff(c_796, plain, (![D_118]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_118)=k10_relat_1('#skF_3', D_118))), inference(resolution, [status(thm)], [c_52, c_793])).
% 3.66/1.63  tff(c_362, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.66/1.63  tff(c_366, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_362])).
% 3.66/1.63  tff(c_50, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.66/1.63  tff(c_105, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.66/1.63  tff(c_367, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_105])).
% 3.66/1.63  tff(c_797, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_367])).
% 3.66/1.63  tff(c_830, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_829, c_797])).
% 3.66/1.63  tff(c_863, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_830])).
% 3.66/1.63  tff(c_870, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_203, c_863])).
% 3.66/1.63  tff(c_874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_870])).
% 3.66/1.63  tff(c_875, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.66/1.63  tff(c_1393, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1392, c_875])).
% 3.66/1.63  tff(c_1394, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_982, c_1393])).
% 3.66/1.63  tff(c_1577, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1576, c_1394])).
% 3.66/1.63  tff(c_1595, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1577])).
% 3.66/1.63  tff(c_1597, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_1595])).
% 3.66/1.63  tff(c_884, plain, (![C_131, B_132, A_133]: (v5_relat_1(C_131, B_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.66/1.63  tff(c_888, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_884])).
% 3.66/1.63  tff(c_1056, plain, (![B_160, A_161]: (k5_relat_1(B_160, k6_relat_1(A_161))=B_160 | ~r1_tarski(k2_relat_1(B_160), A_161) | ~v1_relat_1(B_160))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.63  tff(c_1070, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=B_9 | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_16, c_1056])).
% 3.66/1.63  tff(c_1320, plain, (![A_180, B_181]: (k10_relat_1(A_180, k1_relat_1(B_181))=k1_relat_1(k5_relat_1(A_180, B_181)) | ~v1_relat_1(B_181) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.66/1.63  tff(c_1337, plain, (![A_180, A_21]: (k1_relat_1(k5_relat_1(A_180, k6_relat_1(A_21)))=k10_relat_1(A_180, A_21) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(A_180))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1320])).
% 3.66/1.63  tff(c_1346, plain, (![A_182, A_183]: (k1_relat_1(k5_relat_1(A_182, k6_relat_1(A_183)))=k10_relat_1(A_182, A_183) | ~v1_relat_1(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1337])).
% 3.66/1.63  tff(c_1654, plain, (![B_205, A_206]: (k10_relat_1(B_205, A_206)=k1_relat_1(B_205) | ~v1_relat_1(B_205) | ~v5_relat_1(B_205, A_206) | ~v1_relat_1(B_205))), inference(superposition, [status(thm), theory('equality')], [c_1070, c_1346])).
% 3.66/1.63  tff(c_1666, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_888, c_1654])).
% 3.66/1.63  tff(c_1676, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_1666])).
% 3.66/1.63  tff(c_1683, plain, (![A_207, B_208, C_209]: (k8_relset_1(A_207, B_208, C_209, B_208)=k1_relset_1(A_207, B_208, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.63  tff(c_1685, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1683])).
% 3.66/1.63  tff(c_1687, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1576, c_1685])).
% 3.66/1.63  tff(c_1689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1597, c_1687])).
% 3.66/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  Inference rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Ref     : 0
% 3.66/1.63  #Sup     : 343
% 3.66/1.63  #Fact    : 0
% 3.66/1.63  #Define  : 0
% 3.66/1.63  #Split   : 1
% 3.66/1.63  #Chain   : 0
% 3.66/1.63  #Close   : 0
% 3.66/1.63  
% 3.66/1.63  Ordering : KBO
% 3.66/1.63  
% 3.66/1.63  Simplification rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Subsume      : 12
% 3.66/1.63  #Demod        : 282
% 3.66/1.63  #Tautology    : 197
% 3.66/1.63  #SimpNegUnit  : 1
% 3.66/1.63  #BackRed      : 11
% 3.66/1.63  
% 3.66/1.63  #Partial instantiations: 0
% 3.66/1.63  #Strategies tried      : 1
% 3.66/1.63  
% 3.66/1.63  Timing (in seconds)
% 3.66/1.63  ----------------------
% 3.66/1.63  Preprocessing        : 0.36
% 3.66/1.63  Parsing              : 0.20
% 3.66/1.63  CNF conversion       : 0.02
% 3.66/1.63  Main loop            : 0.44
% 3.66/1.63  Inferencing          : 0.17
% 3.66/1.63  Reduction            : 0.14
% 3.66/1.63  Demodulation         : 0.10
% 3.66/1.63  BG Simplification    : 0.02
% 3.66/1.63  Subsumption          : 0.07
% 3.66/1.63  Abstraction          : 0.03
% 3.66/1.63  MUC search           : 0.00
% 3.66/1.63  Cooper               : 0.00
% 3.66/1.63  Total                : 0.84
% 3.66/1.63  Index Insertion      : 0.00
% 3.66/1.63  Index Deletion       : 0.00
% 3.66/1.63  Index Matching       : 0.00
% 3.66/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
