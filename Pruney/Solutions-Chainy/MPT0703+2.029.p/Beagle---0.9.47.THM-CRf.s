%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 32.87s
% Output     : CNFRefutation 32.87s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 443 expanded)
%              Number of leaves         :   26 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          :  163 ( 843 expanded)
%              Number of equality atoms :   51 ( 187 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(k2_xboole_0(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_36,B_38] : r1_tarski(A_36,k2_xboole_0(A_36,B_38)) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_521,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(k4_xboole_0(A_71,B_72),C_73)
      | ~ r1_tarski(A_71,k2_xboole_0(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2165,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_xboole_0(k4_xboole_0(A_144,B_145),C_146) = C_146
      | ~ r1_tarski(A_144,k2_xboole_0(B_145,C_146)) ) ),
    inference(resolution,[status(thm)],[c_521,c_10])).

tff(c_2333,plain,(
    ! [A_147,B_148] : k2_xboole_0(k4_xboole_0(A_147,A_147),B_148) = B_148 ),
    inference(resolution,[status(thm)],[c_101,c_2165])).

tff(c_312,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k2_xboole_0(B_58,C_59))
      | ~ r1_tarski(k4_xboole_0(A_57,B_58),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_343,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(B_58,k4_xboole_0(A_57,B_58))) ),
    inference(resolution,[status(thm)],[c_6,c_312])).

tff(c_3231,plain,(
    ! [A_155,A_156] : r1_tarski(A_155,k4_xboole_0(A_155,k4_xboole_0(A_156,A_156))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_343])).

tff(c_18,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k2_xboole_0(A_16,C_18),B_17)
      | ~ r1_tarski(C_18,B_17)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1823,plain,(
    ! [A_138,B_139] :
      ( k2_xboole_0(A_138,B_139) = A_138
      | ~ r1_tarski(k2_xboole_0(A_138,B_139),A_138) ) ),
    inference(resolution,[status(thm)],[c_101,c_136])).

tff(c_1833,plain,(
    ! [B_17,C_18] :
      ( k2_xboole_0(B_17,C_18) = B_17
      | ~ r1_tarski(C_18,B_17)
      | ~ r1_tarski(B_17,B_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_1823])).

tff(c_1860,plain,(
    ! [B_17,C_18] :
      ( k2_xboole_0(B_17,C_18) = B_17
      | ~ r1_tarski(C_18,B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1833])).

tff(c_3234,plain,(
    ! [A_155,A_156] : k2_xboole_0(k4_xboole_0(A_155,k4_xboole_0(A_156,A_156)),A_155) = k4_xboole_0(A_155,k4_xboole_0(A_156,A_156)) ),
    inference(resolution,[status(thm)],[c_3231,c_1860])).

tff(c_3280,plain,(
    ! [A_155,A_156] : k4_xboole_0(A_155,k4_xboole_0(A_156,A_156)) = A_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3234])).

tff(c_2478,plain,(
    ! [A_147,B_148] : r1_tarski(k4_xboole_0(A_147,A_147),B_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_101])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [C_23,A_21,B_22] :
      ( k6_subset_1(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k6_subset_1(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_35,plain,(
    ! [C_23,A_21,B_22] :
      ( k4_xboole_0(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k4_xboole_0(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_61,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_102,plain,(
    ! [A_39,B_40] : r1_tarski(A_39,k2_xboole_0(A_39,B_40)) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [A_3,B_4,B_40] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_40)) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_5240,plain,(
    ! [A_181,B_182,B_183] : k2_xboole_0(k4_xboole_0(A_181,k2_xboole_0(A_181,B_182)),B_183) = B_183 ),
    inference(resolution,[status(thm)],[c_119,c_2165])).

tff(c_9239,plain,(
    ! [B_227] : k2_xboole_0(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),B_227) = B_227 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_5240])).

tff(c_9457,plain,(
    ! [B_227] :
      ( k2_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_227) = B_227
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_9239])).

tff(c_10794,plain,(
    ! [B_238] : k2_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_238) = B_238 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_9457])).

tff(c_2561,plain,(
    ! [A_149,B_150] : r1_tarski(k4_xboole_0(A_149,A_149),B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_101])).

tff(c_2589,plain,(
    ! [B_150,A_149] : k2_xboole_0(B_150,k4_xboole_0(A_149,A_149)) = B_150 ),
    inference(resolution,[status(thm)],[c_2561,c_1860])).

tff(c_10862,plain,(
    ! [A_149] : k4_xboole_0(A_149,A_149) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10794,c_2589])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1869,plain,(
    ! [B_140,C_141] :
      ( k2_xboole_0(B_140,C_141) = B_140
      | ~ r1_tarski(C_141,B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1833])).

tff(c_2016,plain,(
    k2_xboole_0(k2_relat_1('#skF_3'),'#skF_1') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1869])).

tff(c_591,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(k4_xboole_0(A_77,B_78),C_79)
      | ~ r1_tarski(A_77,C_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_87])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,k2_xboole_0(B_14,C_15))
      | ~ r1_tarski(k4_xboole_0(A_13,B_14),C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_600,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(A_77,k2_xboole_0(B_78,C_79))
      | ~ r1_tarski(A_77,C_79) ) ),
    inference(resolution,[status(thm)],[c_591,c_16])).

tff(c_3489,plain,(
    ! [A_160] :
      ( r1_tarski(A_160,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_160,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2016,c_600])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( k9_relat_1(B_25,k10_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k2_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3506,plain,(
    ! [A_160] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_160)) = A_160
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_160,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3489,c_24])).

tff(c_120475,plain,(
    ! [A_841] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_841)) = A_841
      | ~ r1_tarski(A_841,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3506])).

tff(c_120561,plain,(
    ! [A_149] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_149,A_149)) = k4_xboole_0('#skF_1','#skF_2')
      | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10862,c_120475])).

tff(c_120633,plain,(
    ! [A_149] : k9_relat_1('#skF_3',k4_xboole_0(A_149,A_149)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_120561])).

tff(c_63,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_180,plain,(
    ! [A_45,B_46,B_47] : r1_tarski(A_45,k2_xboole_0(k2_xboole_0(A_45,B_46),B_47)) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_217,plain,(
    ! [A_48,B_49,B_50] : r1_tarski(k4_xboole_0(A_48,B_49),k2_xboole_0(A_48,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_180])).

tff(c_234,plain,(
    ! [B_49] : r1_tarski(k4_xboole_0('#skF_1',B_49),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_217])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5755,plain,(
    ! [A_190,B_191,C_192] :
      ( k4_xboole_0(A_190,B_191) = C_192
      | ~ r1_tarski(C_192,k4_xboole_0(A_190,B_191))
      | ~ r1_tarski(A_190,k2_xboole_0(B_191,C_192)) ) ),
    inference(resolution,[status(thm)],[c_521,c_2])).

tff(c_53771,plain,(
    ! [A_513,B_514,A_511,B_512] :
      ( k4_xboole_0(A_513,B_514) = k4_xboole_0(A_511,B_512)
      | ~ r1_tarski(A_511,k2_xboole_0(B_512,k4_xboole_0(A_513,B_514)))
      | ~ r1_tarski(A_513,k2_xboole_0(B_514,k4_xboole_0(A_511,B_512))) ) ),
    inference(resolution,[status(thm)],[c_14,c_5755])).

tff(c_54096,plain,(
    ! [A_513,B_514,A_36] :
      ( k4_xboole_0(A_513,B_514) = k4_xboole_0(A_36,A_36)
      | ~ r1_tarski(A_513,k2_xboole_0(B_514,k4_xboole_0(A_36,A_36))) ) ),
    inference(resolution,[status(thm)],[c_101,c_53771])).

tff(c_55337,plain,(
    ! [A_521,A_519,B_520] :
      ( k4_xboole_0(A_521,A_521) = k4_xboole_0(A_519,B_520)
      | ~ r1_tarski(A_519,B_520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_54096])).

tff(c_55629,plain,(
    ! [B_49,A_521] : k4_xboole_0(k4_xboole_0('#skF_1',B_49),k2_relat_1('#skF_3')) = k4_xboole_0(A_521,A_521) ),
    inference(resolution,[status(thm)],[c_234,c_55337])).

tff(c_5409,plain,(
    ! [A_181,B_182,B_183] : r1_tarski(k4_xboole_0(A_181,k2_xboole_0(A_181,B_182)),B_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_5240,c_101])).

tff(c_118019,plain,(
    ! [B_833,B_834] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_833),B_834) ),
    inference(superposition,[status(thm),theory(equality)],[c_10794,c_5409])).

tff(c_118227,plain,(
    ! [B_22,B_834] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_22)),B_834)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_118019])).

tff(c_144412,plain,(
    ! [B_941,B_942] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_941)),B_942) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_118227])).

tff(c_144717,plain,(
    ! [A_943,B_944] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(A_943,A_943)),B_944) ),
    inference(superposition,[status(thm),theory(equality)],[c_55629,c_144412])).

tff(c_2756,plain,(
    ! [B_151,A_152] : k2_xboole_0(B_151,k4_xboole_0(A_152,A_152)) = B_151 ),
    inference(resolution,[status(thm)],[c_2561,c_1860])).

tff(c_2330,plain,(
    ! [A_36,B_38] : k2_xboole_0(k4_xboole_0(A_36,A_36),B_38) = B_38 ),
    inference(resolution,[status(thm)],[c_101,c_2165])).

tff(c_2763,plain,(
    ! [A_36,A_152] : k4_xboole_0(A_36,A_36) = k4_xboole_0(A_152,A_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_2330])).

tff(c_5782,plain,(
    ! [A_36,C_192,A_152] :
      ( k4_xboole_0(A_36,A_36) = C_192
      | ~ r1_tarski(C_192,k4_xboole_0(A_152,A_152))
      | ~ r1_tarski(A_36,k2_xboole_0(A_36,C_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_5755])).

tff(c_5821,plain,(
    ! [A_36,C_192,A_152] :
      ( k4_xboole_0(A_36,A_36) = C_192
      | ~ r1_tarski(C_192,k4_xboole_0(A_152,A_152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5782])).

tff(c_147056,plain,(
    ! [A_949,A_950] : k4_xboole_0(A_949,A_949) = k10_relat_1('#skF_3',k4_xboole_0(A_950,A_950)) ),
    inference(resolution,[status(thm)],[c_144717,c_5821])).

tff(c_3534,plain,(
    ! [A_160] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_160)) = A_160
      | ~ r1_tarski(A_160,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3506])).

tff(c_147169,plain,(
    ! [A_949,A_950] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_949,A_949)) = k4_xboole_0(A_950,A_950)
      | ~ r1_tarski(k4_xboole_0(A_950,A_950),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147056,c_3534])).

tff(c_148126,plain,(
    ! [A_951] : k4_xboole_0(A_951,A_951) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_120633,c_147169])).

tff(c_344,plain,(
    ! [A_60,B_61] : r1_tarski(A_60,k2_xboole_0(B_61,A_60)) ),
    inference(resolution,[status(thm)],[c_12,c_312])).

tff(c_381,plain,(
    ! [A_60,B_61] : k2_xboole_0(A_60,k2_xboole_0(B_61,A_60)) = k2_xboole_0(B_61,A_60) ),
    inference(resolution,[status(thm)],[c_344,c_10])).

tff(c_1427,plain,(
    ! [A_120,B_121,B_122] : r1_tarski(A_120,k2_xboole_0(B_121,k2_xboole_0(k4_xboole_0(A_120,B_121),B_122))) ),
    inference(resolution,[status(thm)],[c_101,c_312])).

tff(c_1462,plain,(
    ! [A_120,A_60] : r1_tarski(A_120,k2_xboole_0(k4_xboole_0(A_120,A_60),A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_1427])).

tff(c_7559,plain,(
    ! [A_211,A_212] : k2_xboole_0(k4_xboole_0(A_211,k4_xboole_0(A_211,A_212)),A_212) = A_212 ),
    inference(resolution,[status(thm)],[c_1462,c_2165])).

tff(c_7706,plain,(
    ! [A_211,A_212] : r1_tarski(k4_xboole_0(A_211,k4_xboole_0(A_211,A_212)),A_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_7559,c_101])).

tff(c_148775,plain,(
    ! [A_951] : r1_tarski(k4_xboole_0('#skF_1',k4_xboole_0(A_951,A_951)),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148126,c_7706])).

tff(c_149139,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3280,c_148775])).

tff(c_149141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_149139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:03:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.87/23.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.87/23.65  
% 32.87/23.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.87/23.66  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 32.87/23.66  
% 32.87/23.66  %Foreground sorts:
% 32.87/23.66  
% 32.87/23.66  
% 32.87/23.66  %Background operators:
% 32.87/23.66  
% 32.87/23.66  
% 32.87/23.66  %Foreground operators:
% 32.87/23.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 32.87/23.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.87/23.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 32.87/23.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.87/23.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 32.87/23.66  tff('#skF_2', type, '#skF_2': $i).
% 32.87/23.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 32.87/23.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 32.87/23.66  tff('#skF_3', type, '#skF_3': $i).
% 32.87/23.66  tff('#skF_1', type, '#skF_1': $i).
% 32.87/23.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.87/23.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 32.87/23.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 32.87/23.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.87/23.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.87/23.66  
% 32.87/23.68  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 32.87/23.68  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 32.87/23.68  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 32.87/23.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.87/23.68  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 32.87/23.68  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 32.87/23.68  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 32.87/23.68  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 32.87/23.68  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 32.87/23.68  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 32.87/23.68  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 32.87/23.68  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 32.87/23.68  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 32.87/23.68  tff(c_48, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.87/23.68  tff(c_62, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_48])).
% 32.87/23.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.87/23.68  tff(c_87, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(k2_xboole_0(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 32.87/23.68  tff(c_101, plain, (![A_36, B_38]: (r1_tarski(A_36, k2_xboole_0(A_36, B_38)))), inference(resolution, [status(thm)], [c_6, c_87])).
% 32.87/23.68  tff(c_521, plain, (![A_71, B_72, C_73]: (r1_tarski(k4_xboole_0(A_71, B_72), C_73) | ~r1_tarski(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.87/23.68  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.87/23.68  tff(c_2165, plain, (![A_144, B_145, C_146]: (k2_xboole_0(k4_xboole_0(A_144, B_145), C_146)=C_146 | ~r1_tarski(A_144, k2_xboole_0(B_145, C_146)))), inference(resolution, [status(thm)], [c_521, c_10])).
% 32.87/23.68  tff(c_2333, plain, (![A_147, B_148]: (k2_xboole_0(k4_xboole_0(A_147, A_147), B_148)=B_148)), inference(resolution, [status(thm)], [c_101, c_2165])).
% 32.87/23.68  tff(c_312, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k2_xboole_0(B_58, C_59)) | ~r1_tarski(k4_xboole_0(A_57, B_58), C_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.87/23.68  tff(c_343, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(B_58, k4_xboole_0(A_57, B_58))))), inference(resolution, [status(thm)], [c_6, c_312])).
% 32.87/23.68  tff(c_3231, plain, (![A_155, A_156]: (r1_tarski(A_155, k4_xboole_0(A_155, k4_xboole_0(A_156, A_156))))), inference(superposition, [status(thm), theory('equality')], [c_2333, c_343])).
% 32.87/23.68  tff(c_18, plain, (![A_16, C_18, B_17]: (r1_tarski(k2_xboole_0(A_16, C_18), B_17) | ~r1_tarski(C_18, B_17) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 32.87/23.68  tff(c_136, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.87/23.68  tff(c_1823, plain, (![A_138, B_139]: (k2_xboole_0(A_138, B_139)=A_138 | ~r1_tarski(k2_xboole_0(A_138, B_139), A_138))), inference(resolution, [status(thm)], [c_101, c_136])).
% 32.87/23.68  tff(c_1833, plain, (![B_17, C_18]: (k2_xboole_0(B_17, C_18)=B_17 | ~r1_tarski(C_18, B_17) | ~r1_tarski(B_17, B_17))), inference(resolution, [status(thm)], [c_18, c_1823])).
% 32.87/23.68  tff(c_1860, plain, (![B_17, C_18]: (k2_xboole_0(B_17, C_18)=B_17 | ~r1_tarski(C_18, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1833])).
% 32.87/23.68  tff(c_3234, plain, (![A_155, A_156]: (k2_xboole_0(k4_xboole_0(A_155, k4_xboole_0(A_156, A_156)), A_155)=k4_xboole_0(A_155, k4_xboole_0(A_156, A_156)))), inference(resolution, [status(thm)], [c_3231, c_1860])).
% 32.87/23.68  tff(c_3280, plain, (![A_155, A_156]: (k4_xboole_0(A_155, k4_xboole_0(A_156, A_156))=A_155)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3234])).
% 32.87/23.68  tff(c_2478, plain, (![A_147, B_148]: (r1_tarski(k4_xboole_0(A_147, A_147), B_148))), inference(superposition, [status(thm), theory('equality')], [c_2333, c_101])).
% 32.87/23.68  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 32.87/23.68  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 32.87/23.68  tff(c_20, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 32.87/23.68  tff(c_22, plain, (![C_23, A_21, B_22]: (k6_subset_1(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k6_subset_1(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 32.87/23.68  tff(c_35, plain, (![C_23, A_21, B_22]: (k4_xboole_0(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k4_xboole_0(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 32.87/23.68  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 32.87/23.68  tff(c_61, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_48])).
% 32.87/23.68  tff(c_102, plain, (![A_39, B_40]: (r1_tarski(A_39, k2_xboole_0(A_39, B_40)))), inference(resolution, [status(thm)], [c_6, c_87])).
% 32.87/23.68  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 32.87/23.68  tff(c_119, plain, (![A_3, B_4, B_40]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_40)))), inference(resolution, [status(thm)], [c_102, c_8])).
% 32.87/23.68  tff(c_5240, plain, (![A_181, B_182, B_183]: (k2_xboole_0(k4_xboole_0(A_181, k2_xboole_0(A_181, B_182)), B_183)=B_183)), inference(resolution, [status(thm)], [c_119, c_2165])).
% 32.87/23.68  tff(c_9239, plain, (![B_227]: (k2_xboole_0(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), B_227)=B_227)), inference(superposition, [status(thm), theory('equality')], [c_61, c_5240])).
% 32.87/23.68  tff(c_9457, plain, (![B_227]: (k2_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_227)=B_227 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_9239])).
% 32.87/23.68  tff(c_10794, plain, (![B_238]: (k2_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_238)=B_238)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_9457])).
% 32.87/23.68  tff(c_2561, plain, (![A_149, B_150]: (r1_tarski(k4_xboole_0(A_149, A_149), B_150))), inference(superposition, [status(thm), theory('equality')], [c_2333, c_101])).
% 32.87/23.68  tff(c_2589, plain, (![B_150, A_149]: (k2_xboole_0(B_150, k4_xboole_0(A_149, A_149))=B_150)), inference(resolution, [status(thm)], [c_2561, c_1860])).
% 32.87/23.68  tff(c_10862, plain, (![A_149]: (k4_xboole_0(A_149, A_149)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_10794, c_2589])).
% 32.87/23.68  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 32.87/23.68  tff(c_1869, plain, (![B_140, C_141]: (k2_xboole_0(B_140, C_141)=B_140 | ~r1_tarski(C_141, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1833])).
% 32.87/23.68  tff(c_2016, plain, (k2_xboole_0(k2_relat_1('#skF_3'), '#skF_1')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1869])).
% 32.87/23.68  tff(c_591, plain, (![A_77, B_78, C_79]: (r1_tarski(k4_xboole_0(A_77, B_78), C_79) | ~r1_tarski(A_77, C_79))), inference(superposition, [status(thm), theory('equality')], [c_62, c_87])).
% 32.87/23.68  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, k2_xboole_0(B_14, C_15)) | ~r1_tarski(k4_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.87/23.68  tff(c_600, plain, (![A_77, B_78, C_79]: (r1_tarski(A_77, k2_xboole_0(B_78, C_79)) | ~r1_tarski(A_77, C_79))), inference(resolution, [status(thm)], [c_591, c_16])).
% 32.87/23.68  tff(c_3489, plain, (![A_160]: (r1_tarski(A_160, k2_relat_1('#skF_3')) | ~r1_tarski(A_160, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2016, c_600])).
% 32.87/23.68  tff(c_24, plain, (![B_25, A_24]: (k9_relat_1(B_25, k10_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k2_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 32.87/23.68  tff(c_3506, plain, (![A_160]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_160))=A_160 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_160, '#skF_1'))), inference(resolution, [status(thm)], [c_3489, c_24])).
% 32.87/23.68  tff(c_120475, plain, (![A_841]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_841))=A_841 | ~r1_tarski(A_841, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3506])).
% 32.87/23.68  tff(c_120561, plain, (![A_149]: (k9_relat_1('#skF_3', k4_xboole_0(A_149, A_149))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10862, c_120475])).
% 32.87/23.68  tff(c_120633, plain, (![A_149]: (k9_relat_1('#skF_3', k4_xboole_0(A_149, A_149))=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_120561])).
% 32.87/23.68  tff(c_63, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_48])).
% 32.87/23.68  tff(c_180, plain, (![A_45, B_46, B_47]: (r1_tarski(A_45, k2_xboole_0(k2_xboole_0(A_45, B_46), B_47)))), inference(resolution, [status(thm)], [c_102, c_8])).
% 32.87/23.68  tff(c_217, plain, (![A_48, B_49, B_50]: (r1_tarski(k4_xboole_0(A_48, B_49), k2_xboole_0(A_48, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_180])).
% 32.87/23.68  tff(c_234, plain, (![B_49]: (r1_tarski(k4_xboole_0('#skF_1', B_49), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_63, c_217])).
% 32.87/23.68  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.87/23.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.87/23.68  tff(c_5755, plain, (![A_190, B_191, C_192]: (k4_xboole_0(A_190, B_191)=C_192 | ~r1_tarski(C_192, k4_xboole_0(A_190, B_191)) | ~r1_tarski(A_190, k2_xboole_0(B_191, C_192)))), inference(resolution, [status(thm)], [c_521, c_2])).
% 32.87/23.68  tff(c_53771, plain, (![A_513, B_514, A_511, B_512]: (k4_xboole_0(A_513, B_514)=k4_xboole_0(A_511, B_512) | ~r1_tarski(A_511, k2_xboole_0(B_512, k4_xboole_0(A_513, B_514))) | ~r1_tarski(A_513, k2_xboole_0(B_514, k4_xboole_0(A_511, B_512))))), inference(resolution, [status(thm)], [c_14, c_5755])).
% 32.87/23.68  tff(c_54096, plain, (![A_513, B_514, A_36]: (k4_xboole_0(A_513, B_514)=k4_xboole_0(A_36, A_36) | ~r1_tarski(A_513, k2_xboole_0(B_514, k4_xboole_0(A_36, A_36))))), inference(resolution, [status(thm)], [c_101, c_53771])).
% 32.87/23.68  tff(c_55337, plain, (![A_521, A_519, B_520]: (k4_xboole_0(A_521, A_521)=k4_xboole_0(A_519, B_520) | ~r1_tarski(A_519, B_520))), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_54096])).
% 32.87/23.68  tff(c_55629, plain, (![B_49, A_521]: (k4_xboole_0(k4_xboole_0('#skF_1', B_49), k2_relat_1('#skF_3'))=k4_xboole_0(A_521, A_521))), inference(resolution, [status(thm)], [c_234, c_55337])).
% 32.87/23.68  tff(c_5409, plain, (![A_181, B_182, B_183]: (r1_tarski(k4_xboole_0(A_181, k2_xboole_0(A_181, B_182)), B_183))), inference(superposition, [status(thm), theory('equality')], [c_5240, c_101])).
% 32.87/23.68  tff(c_118019, plain, (![B_833, B_834]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_833), B_834))), inference(superposition, [status(thm), theory('equality')], [c_10794, c_5409])).
% 32.87/23.68  tff(c_118227, plain, (![B_22, B_834]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_22)), B_834) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_118019])).
% 32.87/23.68  tff(c_144412, plain, (![B_941, B_942]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_941)), B_942))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_118227])).
% 32.87/23.68  tff(c_144717, plain, (![A_943, B_944]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(A_943, A_943)), B_944))), inference(superposition, [status(thm), theory('equality')], [c_55629, c_144412])).
% 32.87/23.68  tff(c_2756, plain, (![B_151, A_152]: (k2_xboole_0(B_151, k4_xboole_0(A_152, A_152))=B_151)), inference(resolution, [status(thm)], [c_2561, c_1860])).
% 32.87/23.68  tff(c_2330, plain, (![A_36, B_38]: (k2_xboole_0(k4_xboole_0(A_36, A_36), B_38)=B_38)), inference(resolution, [status(thm)], [c_101, c_2165])).
% 32.87/23.68  tff(c_2763, plain, (![A_36, A_152]: (k4_xboole_0(A_36, A_36)=k4_xboole_0(A_152, A_152))), inference(superposition, [status(thm), theory('equality')], [c_2756, c_2330])).
% 32.87/23.68  tff(c_5782, plain, (![A_36, C_192, A_152]: (k4_xboole_0(A_36, A_36)=C_192 | ~r1_tarski(C_192, k4_xboole_0(A_152, A_152)) | ~r1_tarski(A_36, k2_xboole_0(A_36, C_192)))), inference(superposition, [status(thm), theory('equality')], [c_2763, c_5755])).
% 32.87/23.68  tff(c_5821, plain, (![A_36, C_192, A_152]: (k4_xboole_0(A_36, A_36)=C_192 | ~r1_tarski(C_192, k4_xboole_0(A_152, A_152)))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5782])).
% 32.87/23.68  tff(c_147056, plain, (![A_949, A_950]: (k4_xboole_0(A_949, A_949)=k10_relat_1('#skF_3', k4_xboole_0(A_950, A_950)))), inference(resolution, [status(thm)], [c_144717, c_5821])).
% 32.87/23.68  tff(c_3534, plain, (![A_160]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_160))=A_160 | ~r1_tarski(A_160, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3506])).
% 32.87/23.68  tff(c_147169, plain, (![A_949, A_950]: (k9_relat_1('#skF_3', k4_xboole_0(A_949, A_949))=k4_xboole_0(A_950, A_950) | ~r1_tarski(k4_xboole_0(A_950, A_950), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_147056, c_3534])).
% 32.87/23.68  tff(c_148126, plain, (![A_951]: (k4_xboole_0(A_951, A_951)=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_120633, c_147169])).
% 32.87/23.68  tff(c_344, plain, (![A_60, B_61]: (r1_tarski(A_60, k2_xboole_0(B_61, A_60)))), inference(resolution, [status(thm)], [c_12, c_312])).
% 32.87/23.68  tff(c_381, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k2_xboole_0(B_61, A_60))=k2_xboole_0(B_61, A_60))), inference(resolution, [status(thm)], [c_344, c_10])).
% 32.87/23.68  tff(c_1427, plain, (![A_120, B_121, B_122]: (r1_tarski(A_120, k2_xboole_0(B_121, k2_xboole_0(k4_xboole_0(A_120, B_121), B_122))))), inference(resolution, [status(thm)], [c_101, c_312])).
% 32.87/23.68  tff(c_1462, plain, (![A_120, A_60]: (r1_tarski(A_120, k2_xboole_0(k4_xboole_0(A_120, A_60), A_60)))), inference(superposition, [status(thm), theory('equality')], [c_381, c_1427])).
% 32.87/23.68  tff(c_7559, plain, (![A_211, A_212]: (k2_xboole_0(k4_xboole_0(A_211, k4_xboole_0(A_211, A_212)), A_212)=A_212)), inference(resolution, [status(thm)], [c_1462, c_2165])).
% 32.87/23.68  tff(c_7706, plain, (![A_211, A_212]: (r1_tarski(k4_xboole_0(A_211, k4_xboole_0(A_211, A_212)), A_212))), inference(superposition, [status(thm), theory('equality')], [c_7559, c_101])).
% 32.87/23.68  tff(c_148775, plain, (![A_951]: (r1_tarski(k4_xboole_0('#skF_1', k4_xboole_0(A_951, A_951)), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_148126, c_7706])).
% 32.87/23.68  tff(c_149139, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3280, c_148775])).
% 32.87/23.68  tff(c_149141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_149139])).
% 32.87/23.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.87/23.68  
% 32.87/23.68  Inference rules
% 32.87/23.68  ----------------------
% 32.87/23.68  #Ref     : 0
% 32.87/23.68  #Sup     : 36217
% 32.87/23.68  #Fact    : 0
% 32.87/23.68  #Define  : 0
% 32.87/23.68  #Split   : 6
% 32.87/23.68  #Chain   : 0
% 32.87/23.68  #Close   : 0
% 32.87/23.68  
% 32.87/23.68  Ordering : KBO
% 32.87/23.68  
% 32.87/23.68  Simplification rules
% 32.87/23.68  ----------------------
% 32.87/23.68  #Subsume      : 4583
% 32.87/23.68  #Demod        : 29237
% 32.87/23.68  #Tautology    : 18740
% 32.87/23.68  #SimpNegUnit  : 11
% 32.87/23.68  #BackRed      : 80
% 32.87/23.68  
% 32.87/23.68  #Partial instantiations: 0
% 32.87/23.68  #Strategies tried      : 1
% 32.87/23.68  
% 32.87/23.68  Timing (in seconds)
% 32.87/23.68  ----------------------
% 32.87/23.68  Preprocessing        : 0.30
% 32.87/23.68  Parsing              : 0.16
% 32.87/23.68  CNF conversion       : 0.02
% 32.87/23.68  Main loop            : 22.61
% 32.87/23.68  Inferencing          : 2.13
% 32.87/23.68  Reduction            : 13.64
% 32.87/23.68  Demodulation         : 12.56
% 32.87/23.68  BG Simplification    : 0.29
% 32.87/23.68  Subsumption          : 5.59
% 32.87/23.68  Abstraction          : 0.51
% 32.87/23.68  MUC search           : 0.00
% 32.87/23.68  Cooper               : 0.00
% 32.87/23.68  Total                : 22.96
% 32.87/23.68  Index Insertion      : 0.00
% 33.05/23.68  Index Deletion       : 0.00
% 33.05/23.68  Index Matching       : 0.00
% 33.05/23.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
