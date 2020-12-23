%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 18.21s
% Output     : CNFRefutation 18.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 353 expanded)
%              Number of leaves         :   27 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  162 ( 618 expanded)
%              Number of equality atoms :   51 ( 156 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_652,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(k4_xboole_0(A_77,B_78),C_79)
      | ~ r1_tarski(A_77,k2_xboole_0(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2007,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_xboole_0(k4_xboole_0(A_131,B_132),C_133) = C_133
      | ~ r1_tarski(A_131,k2_xboole_0(B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_652,c_12])).

tff(c_2138,plain,(
    ! [A_134,B_135] : k2_xboole_0(k4_xboole_0(A_134,A_134),B_135) = B_135 ),
    inference(resolution,[status(thm)],[c_20,c_2007])).

tff(c_2267,plain,(
    ! [A_134,B_135] : r1_tarski(k4_xboole_0(A_134,A_134),B_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_20])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1342,plain,(
    ! [A_105,C_106,B_107,B_108] :
      ( r1_tarski(A_105,k2_xboole_0(C_106,B_107))
      | ~ r1_tarski(k2_xboole_0(A_105,B_108),B_107) ) ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_1431,plain,(
    ! [A_112,C_113,B_114] : r1_tarski(A_112,k2_xboole_0(C_113,k2_xboole_0(A_112,B_114))) ),
    inference(resolution,[status(thm)],[c_6,c_1342])).

tff(c_1485,plain,(
    ! [B_2,C_113] : r1_tarski(B_2,k2_xboole_0(C_113,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1431])).

tff(c_2350,plain,(
    ! [B_138,C_139] : k2_xboole_0(k4_xboole_0(B_138,C_139),B_138) = B_138 ),
    inference(resolution,[status(thm)],[c_1485,c_2007])).

tff(c_2451,plain,(
    ! [B_138,C_139] : r1_tarski(k4_xboole_0(B_138,C_139),B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_2350,c_20])).

tff(c_22,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    ! [C_25,A_23,B_24] :
      ( k4_xboole_0(k10_relat_1(C_25,A_23),k10_relat_1(C_25,B_24)) = k10_relat_1(C_25,k4_xboole_0(A_23,B_24))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_24])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_63,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_119,plain,(
    ! [A_39,B_41,B_20] : r1_tarski(A_39,k2_xboole_0(k2_xboole_0(A_39,B_41),B_20)) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_3820,plain,(
    ! [A_174,B_175,B_176] : k2_xboole_0(k4_xboole_0(A_174,k2_xboole_0(A_174,B_175)),B_176) = B_176 ),
    inference(resolution,[status(thm)],[c_119,c_2007])).

tff(c_3978,plain,(
    ! [A_174,B_175,B_176] : r1_tarski(k4_xboole_0(A_174,k2_xboole_0(A_174,B_175)),B_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_3820,c_20])).

tff(c_2136,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,A_19),B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_20,c_2007])).

tff(c_154,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(k2_xboole_0(A_19,B_20),A_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_2229,plain,(
    ! [A_134,B_135] :
      ( k2_xboole_0(k4_xboole_0(A_134,A_134),B_135) = k4_xboole_0(A_134,A_134)
      | ~ r1_tarski(B_135,k4_xboole_0(A_134,A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_173])).

tff(c_11031,plain,(
    ! [A_289,B_290] :
      ( k4_xboole_0(A_289,A_289) = B_290
      | ~ r1_tarski(B_290,k4_xboole_0(A_289,A_289)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_2229])).

tff(c_13868,plain,(
    ! [A_310,B_311,A_309] : k4_xboole_0(A_310,k2_xboole_0(A_310,B_311)) = k4_xboole_0(A_309,A_309) ),
    inference(resolution,[status(thm)],[c_3978,c_11031])).

tff(c_14398,plain,(
    ! [A_312] : k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k4_xboole_0(A_312,A_312) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_13868])).

tff(c_14688,plain,(
    ! [A_312] :
      ( k4_xboole_0(A_312,A_312) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_14398])).

tff(c_18146,plain,(
    ! [A_333] : k4_xboole_0(A_333,A_333) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_14688])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_65,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_301,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_341,plain,(
    ! [A_55,B_56,B_57] :
      ( r1_tarski(A_55,k2_xboole_0(B_56,B_57))
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_119])).

tff(c_369,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_55,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_341])).

tff(c_970,plain,(
    ! [B_94,A_95] :
      ( k9_relat_1(B_94,k10_relat_1(B_94,A_95)) = A_95
      | ~ r1_tarski(A_95,k2_relat_1(B_94))
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_975,plain,(
    ! [A_55] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_55)) = A_55
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_55,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_369,c_970])).

tff(c_984,plain,(
    ! [A_55] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_55)) = A_55
      | ~ r1_tarski(A_55,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_975])).

tff(c_18348,plain,(
    ! [A_333] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_333,A_333)) = k4_xboole_0('#skF_1','#skF_2')
      | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18146,c_984])).

tff(c_18481,plain,(
    ! [A_333] : k9_relat_1('#skF_3',k4_xboole_0(A_333,A_333)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_18348])).

tff(c_2116,plain,(
    ! [B_2,C_113] : k2_xboole_0(k4_xboole_0(B_2,C_113),B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_1485,c_2007])).

tff(c_14280,plain,(
    ! [B_2,C_113,A_309] : k4_xboole_0(k4_xboole_0(B_2,C_113),B_2) = k4_xboole_0(A_309,A_309) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_13868])).

tff(c_5185,plain,(
    ! [B_207] : k2_xboole_0(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),B_207) = B_207 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_3820])).

tff(c_5374,plain,(
    ! [B_207] :
      ( k2_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_207) = B_207
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_5185])).

tff(c_5448,plain,(
    ! [B_208] : k2_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_208) = B_208 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_5374])).

tff(c_78993,plain,(
    ! [B_690,B_691] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_690),B_691) ),
    inference(superposition,[status(thm),theory(equality)],[c_5448,c_3978])).

tff(c_79142,plain,(
    ! [B_24,B_691] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_24)),B_691)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_78993])).

tff(c_81154,plain,(
    ! [B_707,B_708] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_707)),B_708) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_79142])).

tff(c_81335,plain,(
    ! [A_709,B_710] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(A_709,A_709)),B_710) ),
    inference(superposition,[status(thm),theory(equality)],[c_14280,c_81154])).

tff(c_11163,plain,(
    ! [A_292,A_291] : k4_xboole_0(A_292,A_292) = k4_xboole_0(A_291,A_291) ),
    inference(resolution,[status(thm)],[c_2267,c_11031])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_665,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_xboole_0(A_77,B_78) = C_79
      | ~ r1_tarski(C_79,k4_xboole_0(A_77,B_78))
      | ~ r1_tarski(A_77,k2_xboole_0(B_78,C_79)) ) ),
    inference(resolution,[status(thm)],[c_652,c_2])).

tff(c_11295,plain,(
    ! [A_292,C_79,A_291] :
      ( k4_xboole_0(A_292,A_292) = C_79
      | ~ r1_tarski(C_79,k4_xboole_0(A_291,A_291))
      | ~ r1_tarski(A_292,k2_xboole_0(A_292,C_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11163,c_665])).

tff(c_11627,plain,(
    ! [A_292,C_79,A_291] :
      ( k4_xboole_0(A_292,A_292) = C_79
      | ~ r1_tarski(C_79,k4_xboole_0(A_291,A_291)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11295])).

tff(c_82441,plain,(
    ! [A_719,A_720] : k4_xboole_0(A_719,A_719) = k10_relat_1('#skF_3',k4_xboole_0(A_720,A_720)) ),
    inference(resolution,[status(thm)],[c_81335,c_11627])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k4_xboole_0(A_11,B_12),C_13)
      | ~ r1_tarski(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_9401,plain,(
    ! [B_268,A_269,B_270] :
      ( k9_relat_1(B_268,k10_relat_1(B_268,k4_xboole_0(A_269,B_270))) = k4_xboole_0(A_269,B_270)
      | ~ v1_funct_1(B_268)
      | ~ v1_relat_1(B_268)
      | ~ r1_tarski(A_269,k2_xboole_0(B_270,k2_relat_1(B_268))) ) ),
    inference(resolution,[status(thm)],[c_14,c_970])).

tff(c_9620,plain,(
    ! [B_268,A_19] :
      ( k9_relat_1(B_268,k10_relat_1(B_268,k4_xboole_0(A_19,A_19))) = k4_xboole_0(A_19,A_19)
      | ~ v1_funct_1(B_268)
      | ~ v1_relat_1(B_268) ) ),
    inference(resolution,[status(thm)],[c_20,c_9401])).

tff(c_82504,plain,(
    ! [A_719,A_720] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_719,A_719)) = k4_xboole_0(A_720,A_720)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82441,c_9620])).

tff(c_83201,plain,(
    ! [A_721] : k4_xboole_0(A_721,A_721) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_18481,c_82504])).

tff(c_1509,plain,(
    ! [B_115,C_116] : r1_tarski(B_115,k2_xboole_0(C_116,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1431])).

tff(c_1698,plain,(
    ! [B_124,C_125] : k2_xboole_0(B_124,k2_xboole_0(C_125,B_124)) = k2_xboole_0(C_125,B_124) ),
    inference(resolution,[status(thm)],[c_1509,c_12])).

tff(c_393,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k2_xboole_0(B_60,C_61))
      | ~ r1_tarski(k4_xboole_0(A_59,B_60),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_422,plain,(
    ! [A_59,B_60,B_20] : r1_tarski(A_59,k2_xboole_0(B_60,k2_xboole_0(k4_xboole_0(A_59,B_60),B_20))) ),
    inference(resolution,[status(thm)],[c_20,c_393])).

tff(c_1768,plain,(
    ! [A_59,B_124] : r1_tarski(A_59,k2_xboole_0(k4_xboole_0(A_59,B_124),B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1698,c_422])).

tff(c_2110,plain,(
    ! [A_59,B_124] : k2_xboole_0(k4_xboole_0(A_59,k4_xboole_0(A_59,B_124)),B_124) = B_124 ),
    inference(resolution,[status(thm)],[c_1768,c_2007])).

tff(c_88,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,k2_xboole_0(C_37,B_38))
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3267,plain,(
    ! [A_167,C_168,B_169] :
      ( k2_xboole_0(A_167,k2_xboole_0(C_168,B_169)) = k2_xboole_0(C_168,B_169)
      | ~ r1_tarski(A_167,B_169) ) ),
    inference(resolution,[status(thm)],[c_88,c_12])).

tff(c_12776,plain,(
    ! [A_297,A_298,B_299] :
      ( r1_tarski(A_297,k2_xboole_0(k4_xboole_0(A_297,A_298),B_299))
      | ~ r1_tarski(A_298,B_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3267,c_422])).

tff(c_12857,plain,(
    ! [A_59,B_124] :
      ( r1_tarski(A_59,B_124)
      | ~ r1_tarski(k4_xboole_0(A_59,B_124),B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_12776])).

tff(c_83563,plain,(
    ! [A_721] :
      ( r1_tarski('#skF_1','#skF_2')
      | ~ r1_tarski(k4_xboole_0(A_721,A_721),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83201,c_12857])).

tff(c_84024,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2267,c_83563])).

tff(c_84026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_84024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.21/10.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.21/10.84  
% 18.21/10.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.21/10.84  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 18.21/10.84  
% 18.21/10.84  %Foreground sorts:
% 18.21/10.84  
% 18.21/10.84  
% 18.21/10.84  %Background operators:
% 18.21/10.84  
% 18.21/10.84  
% 18.21/10.84  %Foreground operators:
% 18.21/10.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.21/10.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.21/10.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.21/10.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.21/10.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.21/10.84  tff('#skF_2', type, '#skF_2': $i).
% 18.21/10.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.21/10.84  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 18.21/10.84  tff('#skF_3', type, '#skF_3': $i).
% 18.21/10.84  tff('#skF_1', type, '#skF_1': $i).
% 18.21/10.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.21/10.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 18.21/10.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.21/10.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.21/10.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.21/10.84  
% 18.21/10.86  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 18.21/10.86  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.21/10.86  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 18.21/10.86  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.21/10.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.21/10.86  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 18.21/10.86  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 18.21/10.86  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 18.21/10.86  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 18.21/10.86  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 18.21/10.86  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 18.21/10.86  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 18.21/10.86  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.21/10.86  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.21/10.86  tff(c_652, plain, (![A_77, B_78, C_79]: (r1_tarski(k4_xboole_0(A_77, B_78), C_79) | ~r1_tarski(A_77, k2_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.21/10.86  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.21/10.86  tff(c_2007, plain, (![A_131, B_132, C_133]: (k2_xboole_0(k4_xboole_0(A_131, B_132), C_133)=C_133 | ~r1_tarski(A_131, k2_xboole_0(B_132, C_133)))), inference(resolution, [status(thm)], [c_652, c_12])).
% 18.21/10.86  tff(c_2138, plain, (![A_134, B_135]: (k2_xboole_0(k4_xboole_0(A_134, A_134), B_135)=B_135)), inference(resolution, [status(thm)], [c_20, c_2007])).
% 18.21/10.86  tff(c_2267, plain, (![A_134, B_135]: (r1_tarski(k4_xboole_0(A_134, A_134), B_135))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_20])).
% 18.21/10.86  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.21/10.86  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.21/10.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.21/10.86  tff(c_50, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.21/10.86  tff(c_66, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_50])).
% 18.21/10.86  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.21/10.86  tff(c_99, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.21/10.86  tff(c_1342, plain, (![A_105, C_106, B_107, B_108]: (r1_tarski(A_105, k2_xboole_0(C_106, B_107)) | ~r1_tarski(k2_xboole_0(A_105, B_108), B_107))), inference(resolution, [status(thm)], [c_8, c_99])).
% 18.21/10.86  tff(c_1431, plain, (![A_112, C_113, B_114]: (r1_tarski(A_112, k2_xboole_0(C_113, k2_xboole_0(A_112, B_114))))), inference(resolution, [status(thm)], [c_6, c_1342])).
% 18.21/10.86  tff(c_1485, plain, (![B_2, C_113]: (r1_tarski(B_2, k2_xboole_0(C_113, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1431])).
% 18.21/10.86  tff(c_2350, plain, (![B_138, C_139]: (k2_xboole_0(k4_xboole_0(B_138, C_139), B_138)=B_138)), inference(resolution, [status(thm)], [c_1485, c_2007])).
% 18.21/10.86  tff(c_2451, plain, (![B_138, C_139]: (r1_tarski(k4_xboole_0(B_138, C_139), B_138))), inference(superposition, [status(thm), theory('equality')], [c_2350, c_20])).
% 18.21/10.86  tff(c_22, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.21/10.86  tff(c_24, plain, (![C_25, A_23, B_24]: (k6_subset_1(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.21/10.86  tff(c_37, plain, (![C_25, A_23, B_24]: (k4_xboole_0(k10_relat_1(C_25, A_23), k10_relat_1(C_25, B_24))=k10_relat_1(C_25, k4_xboole_0(A_23, B_24)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_24])).
% 18.21/10.86  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.21/10.86  tff(c_63, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_50])).
% 18.21/10.86  tff(c_119, plain, (![A_39, B_41, B_20]: (r1_tarski(A_39, k2_xboole_0(k2_xboole_0(A_39, B_41), B_20)))), inference(resolution, [status(thm)], [c_20, c_99])).
% 18.21/10.86  tff(c_3820, plain, (![A_174, B_175, B_176]: (k2_xboole_0(k4_xboole_0(A_174, k2_xboole_0(A_174, B_175)), B_176)=B_176)), inference(resolution, [status(thm)], [c_119, c_2007])).
% 18.21/10.86  tff(c_3978, plain, (![A_174, B_175, B_176]: (r1_tarski(k4_xboole_0(A_174, k2_xboole_0(A_174, B_175)), B_176))), inference(superposition, [status(thm), theory('equality')], [c_3820, c_20])).
% 18.21/10.86  tff(c_2136, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, A_19), B_20)=B_20)), inference(resolution, [status(thm)], [c_20, c_2007])).
% 18.21/10.86  tff(c_154, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.21/10.86  tff(c_173, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(k2_xboole_0(A_19, B_20), A_19))), inference(resolution, [status(thm)], [c_20, c_154])).
% 18.21/10.86  tff(c_2229, plain, (![A_134, B_135]: (k2_xboole_0(k4_xboole_0(A_134, A_134), B_135)=k4_xboole_0(A_134, A_134) | ~r1_tarski(B_135, k4_xboole_0(A_134, A_134)))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_173])).
% 18.21/10.86  tff(c_11031, plain, (![A_289, B_290]: (k4_xboole_0(A_289, A_289)=B_290 | ~r1_tarski(B_290, k4_xboole_0(A_289, A_289)))), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_2229])).
% 18.21/10.86  tff(c_13868, plain, (![A_310, B_311, A_309]: (k4_xboole_0(A_310, k2_xboole_0(A_310, B_311))=k4_xboole_0(A_309, A_309))), inference(resolution, [status(thm)], [c_3978, c_11031])).
% 18.21/10.86  tff(c_14398, plain, (![A_312]: (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k4_xboole_0(A_312, A_312))), inference(superposition, [status(thm), theory('equality')], [c_63, c_13868])).
% 18.21/10.86  tff(c_14688, plain, (![A_312]: (k4_xboole_0(A_312, A_312)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_14398])).
% 18.21/10.86  tff(c_18146, plain, (![A_333]: (k4_xboole_0(A_333, A_333)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_14688])).
% 18.21/10.86  tff(c_30, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.21/10.86  tff(c_65, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_50])).
% 18.21/10.86  tff(c_301, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.21/10.86  tff(c_341, plain, (![A_55, B_56, B_57]: (r1_tarski(A_55, k2_xboole_0(B_56, B_57)) | ~r1_tarski(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_301, c_119])).
% 18.21/10.86  tff(c_369, plain, (![A_55]: (r1_tarski(A_55, k2_relat_1('#skF_3')) | ~r1_tarski(A_55, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_341])).
% 18.21/10.86  tff(c_970, plain, (![B_94, A_95]: (k9_relat_1(B_94, k10_relat_1(B_94, A_95))=A_95 | ~r1_tarski(A_95, k2_relat_1(B_94)) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.21/10.86  tff(c_975, plain, (![A_55]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_55))=A_55 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_55, '#skF_1'))), inference(resolution, [status(thm)], [c_369, c_970])).
% 18.21/10.86  tff(c_984, plain, (![A_55]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_55))=A_55 | ~r1_tarski(A_55, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_975])).
% 18.21/10.86  tff(c_18348, plain, (![A_333]: (k9_relat_1('#skF_3', k4_xboole_0(A_333, A_333))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18146, c_984])).
% 18.21/10.86  tff(c_18481, plain, (![A_333]: (k9_relat_1('#skF_3', k4_xboole_0(A_333, A_333))=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_18348])).
% 18.21/10.86  tff(c_2116, plain, (![B_2, C_113]: (k2_xboole_0(k4_xboole_0(B_2, C_113), B_2)=B_2)), inference(resolution, [status(thm)], [c_1485, c_2007])).
% 18.21/10.86  tff(c_14280, plain, (![B_2, C_113, A_309]: (k4_xboole_0(k4_xboole_0(B_2, C_113), B_2)=k4_xboole_0(A_309, A_309))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_13868])).
% 18.21/10.86  tff(c_5185, plain, (![B_207]: (k2_xboole_0(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), B_207)=B_207)), inference(superposition, [status(thm), theory('equality')], [c_63, c_3820])).
% 18.21/10.86  tff(c_5374, plain, (![B_207]: (k2_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_207)=B_207 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_5185])).
% 18.21/10.86  tff(c_5448, plain, (![B_208]: (k2_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_208)=B_208)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_5374])).
% 18.21/10.86  tff(c_78993, plain, (![B_690, B_691]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_690), B_691))), inference(superposition, [status(thm), theory('equality')], [c_5448, c_3978])).
% 18.21/10.86  tff(c_79142, plain, (![B_24, B_691]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_24)), B_691) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_78993])).
% 18.21/10.86  tff(c_81154, plain, (![B_707, B_708]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_707)), B_708))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_79142])).
% 18.21/10.86  tff(c_81335, plain, (![A_709, B_710]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(A_709, A_709)), B_710))), inference(superposition, [status(thm), theory('equality')], [c_14280, c_81154])).
% 18.21/10.86  tff(c_11163, plain, (![A_292, A_291]: (k4_xboole_0(A_292, A_292)=k4_xboole_0(A_291, A_291))), inference(resolution, [status(thm)], [c_2267, c_11031])).
% 18.21/10.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.21/10.86  tff(c_665, plain, (![A_77, B_78, C_79]: (k4_xboole_0(A_77, B_78)=C_79 | ~r1_tarski(C_79, k4_xboole_0(A_77, B_78)) | ~r1_tarski(A_77, k2_xboole_0(B_78, C_79)))), inference(resolution, [status(thm)], [c_652, c_2])).
% 18.21/10.86  tff(c_11295, plain, (![A_292, C_79, A_291]: (k4_xboole_0(A_292, A_292)=C_79 | ~r1_tarski(C_79, k4_xboole_0(A_291, A_291)) | ~r1_tarski(A_292, k2_xboole_0(A_292, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_11163, c_665])).
% 18.21/10.86  tff(c_11627, plain, (![A_292, C_79, A_291]: (k4_xboole_0(A_292, A_292)=C_79 | ~r1_tarski(C_79, k4_xboole_0(A_291, A_291)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11295])).
% 18.21/10.86  tff(c_82441, plain, (![A_719, A_720]: (k4_xboole_0(A_719, A_719)=k10_relat_1('#skF_3', k4_xboole_0(A_720, A_720)))), inference(resolution, [status(thm)], [c_81335, c_11627])).
% 18.21/10.86  tff(c_14, plain, (![A_11, B_12, C_13]: (r1_tarski(k4_xboole_0(A_11, B_12), C_13) | ~r1_tarski(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.21/10.86  tff(c_9401, plain, (![B_268, A_269, B_270]: (k9_relat_1(B_268, k10_relat_1(B_268, k4_xboole_0(A_269, B_270)))=k4_xboole_0(A_269, B_270) | ~v1_funct_1(B_268) | ~v1_relat_1(B_268) | ~r1_tarski(A_269, k2_xboole_0(B_270, k2_relat_1(B_268))))), inference(resolution, [status(thm)], [c_14, c_970])).
% 18.21/10.86  tff(c_9620, plain, (![B_268, A_19]: (k9_relat_1(B_268, k10_relat_1(B_268, k4_xboole_0(A_19, A_19)))=k4_xboole_0(A_19, A_19) | ~v1_funct_1(B_268) | ~v1_relat_1(B_268))), inference(resolution, [status(thm)], [c_20, c_9401])).
% 18.21/10.86  tff(c_82504, plain, (![A_719, A_720]: (k9_relat_1('#skF_3', k4_xboole_0(A_719, A_719))=k4_xboole_0(A_720, A_720) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_82441, c_9620])).
% 18.21/10.86  tff(c_83201, plain, (![A_721]: (k4_xboole_0(A_721, A_721)=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_18481, c_82504])).
% 18.21/10.86  tff(c_1509, plain, (![B_115, C_116]: (r1_tarski(B_115, k2_xboole_0(C_116, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1431])).
% 18.21/10.86  tff(c_1698, plain, (![B_124, C_125]: (k2_xboole_0(B_124, k2_xboole_0(C_125, B_124))=k2_xboole_0(C_125, B_124))), inference(resolution, [status(thm)], [c_1509, c_12])).
% 18.21/10.86  tff(c_393, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k2_xboole_0(B_60, C_61)) | ~r1_tarski(k4_xboole_0(A_59, B_60), C_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.21/10.86  tff(c_422, plain, (![A_59, B_60, B_20]: (r1_tarski(A_59, k2_xboole_0(B_60, k2_xboole_0(k4_xboole_0(A_59, B_60), B_20))))), inference(resolution, [status(thm)], [c_20, c_393])).
% 18.21/10.86  tff(c_1768, plain, (![A_59, B_124]: (r1_tarski(A_59, k2_xboole_0(k4_xboole_0(A_59, B_124), B_124)))), inference(superposition, [status(thm), theory('equality')], [c_1698, c_422])).
% 18.21/10.86  tff(c_2110, plain, (![A_59, B_124]: (k2_xboole_0(k4_xboole_0(A_59, k4_xboole_0(A_59, B_124)), B_124)=B_124)), inference(resolution, [status(thm)], [c_1768, c_2007])).
% 18.21/10.86  tff(c_88, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, k2_xboole_0(C_37, B_38)) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.21/10.86  tff(c_3267, plain, (![A_167, C_168, B_169]: (k2_xboole_0(A_167, k2_xboole_0(C_168, B_169))=k2_xboole_0(C_168, B_169) | ~r1_tarski(A_167, B_169))), inference(resolution, [status(thm)], [c_88, c_12])).
% 18.21/10.86  tff(c_12776, plain, (![A_297, A_298, B_299]: (r1_tarski(A_297, k2_xboole_0(k4_xboole_0(A_297, A_298), B_299)) | ~r1_tarski(A_298, B_299))), inference(superposition, [status(thm), theory('equality')], [c_3267, c_422])).
% 18.21/10.86  tff(c_12857, plain, (![A_59, B_124]: (r1_tarski(A_59, B_124) | ~r1_tarski(k4_xboole_0(A_59, B_124), B_124))), inference(superposition, [status(thm), theory('equality')], [c_2110, c_12776])).
% 18.21/10.86  tff(c_83563, plain, (![A_721]: (r1_tarski('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0(A_721, A_721), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_83201, c_12857])).
% 18.21/10.86  tff(c_84024, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2267, c_83563])).
% 18.21/10.86  tff(c_84026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_84024])).
% 18.21/10.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.21/10.86  
% 18.21/10.86  Inference rules
% 18.21/10.86  ----------------------
% 18.21/10.86  #Ref     : 0
% 18.21/10.86  #Sup     : 20426
% 18.21/10.86  #Fact    : 0
% 18.21/10.86  #Define  : 0
% 18.21/10.86  #Split   : 4
% 18.21/10.86  #Chain   : 0
% 18.21/10.86  #Close   : 0
% 18.21/10.86  
% 18.21/10.86  Ordering : KBO
% 18.21/10.86  
% 18.21/10.86  Simplification rules
% 18.21/10.86  ----------------------
% 18.21/10.86  #Subsume      : 2082
% 18.21/10.86  #Demod        : 14326
% 18.21/10.86  #Tautology    : 11030
% 18.21/10.86  #SimpNegUnit  : 7
% 18.21/10.86  #BackRed      : 7
% 18.21/10.86  
% 18.21/10.86  #Partial instantiations: 0
% 18.21/10.86  #Strategies tried      : 1
% 18.21/10.86  
% 18.21/10.86  Timing (in seconds)
% 18.21/10.86  ----------------------
% 18.21/10.86  Preprocessing        : 0.30
% 18.21/10.86  Parsing              : 0.16
% 18.21/10.86  CNF conversion       : 0.02
% 18.21/10.87  Main loop            : 9.78
% 18.21/10.87  Inferencing          : 1.25
% 18.21/10.87  Reduction            : 5.52
% 18.21/10.87  Demodulation         : 4.96
% 18.21/10.87  BG Simplification    : 0.15
% 18.21/10.87  Subsumption          : 2.44
% 18.21/10.87  Abstraction          : 0.25
% 18.21/10.87  MUC search           : 0.00
% 18.21/10.87  Cooper               : 0.00
% 18.21/10.87  Total                : 10.12
% 18.21/10.87  Index Insertion      : 0.00
% 18.21/10.87  Index Deletion       : 0.00
% 18.21/10.87  Index Matching       : 0.00
% 18.21/10.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
