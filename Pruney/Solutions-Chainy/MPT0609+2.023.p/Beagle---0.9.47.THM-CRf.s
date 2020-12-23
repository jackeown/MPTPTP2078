%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 837 expanded)
%              Number of leaves         :   33 ( 323 expanded)
%              Depth                    :   19
%              Number of atoms          :   89 (1071 expanded)
%              Number of equality atoms :   55 ( 769 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_179,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_182,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_30,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [C_44,A_42,B_43] :
      ( k6_subset_1(k7_relat_1(C_44,A_42),k7_relat_1(C_44,B_43)) = k7_relat_1(C_44,k6_subset_1(A_42,B_43))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_429,plain,(
    ! [C_102,A_103,B_104] :
      ( k4_xboole_0(k7_relat_1(C_102,A_103),k7_relat_1(C_102,B_104)) = k7_relat_1(C_102,k4_xboole_0(A_103,B_104))
      | ~ v1_relat_1(C_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_34])).

tff(c_439,plain,(
    ! [C_102,B_104] :
      ( k7_relat_1(C_102,k4_xboole_0(B_104,B_104)) = k1_xboole_0
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_182])).

tff(c_455,plain,(
    ! [C_105] :
      ( k7_relat_1(C_105,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_439])).

tff(c_459,plain,(
    k7_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_455])).

tff(c_38,plain,(
    ! [B_49,A_48] :
      ( k1_relat_1(k6_subset_1(B_49,k7_relat_1(B_49,A_48))) = k6_subset_1(k1_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_325,plain,(
    ! [B_85,A_86] :
      ( k1_relat_1(k4_xboole_0(B_85,k7_relat_1(B_85,A_86))) = k4_xboole_0(k1_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_38])).

tff(c_40,plain,(
    ! [B_51,A_50] :
      ( k3_xboole_0(k1_relat_1(B_51),A_50) = k1_relat_1(k7_relat_1(B_51,A_50))
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1547,plain,(
    ! [B_145,A_146,A_147] :
      ( k1_relat_1(k7_relat_1(k4_xboole_0(B_145,k7_relat_1(B_145,A_146)),A_147)) = k3_xboole_0(k4_xboole_0(k1_relat_1(B_145),A_146),A_147)
      | ~ v1_relat_1(k4_xboole_0(B_145,k7_relat_1(B_145,A_146)))
      | ~ v1_relat_1(B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_40])).

tff(c_1616,plain,(
    ! [A_147] :
      ( k3_xboole_0(k4_xboole_0(k1_relat_1('#skF_2'),k1_xboole_0),A_147) = k1_relat_1(k7_relat_1(k4_xboole_0('#skF_2',k1_xboole_0),A_147))
      | ~ v1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2',k1_xboole_0)))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_1547])).

tff(c_1638,plain,(
    ! [A_148] : k3_xboole_0(k1_relat_1('#skF_2'),A_148) = k1_relat_1(k7_relat_1('#skF_2',A_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_14,c_459,c_14,c_14,c_1616])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1677,plain,(
    ! [A_148] : k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2',A_148))) = k4_xboole_0(k1_relat_1('#skF_2'),A_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_10])).

tff(c_1636,plain,(
    ! [A_147] : k3_xboole_0(k1_relat_1('#skF_2'),A_147) = k1_relat_1(k7_relat_1('#skF_2',A_147)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_14,c_459,c_14,c_14,c_1616])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,k4_xboole_0(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_16])).

tff(c_45,plain,(
    ! [B_49,A_48] :
      ( k1_relat_1(k4_xboole_0(B_49,k7_relat_1(B_49,A_48))) = k4_xboole_0(k1_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_38])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [C_47,A_45,B_46] :
      ( k7_relat_1(C_47,k6_subset_1(A_45,B_46)) = k6_subset_1(C_47,k7_relat_1(C_47,B_46))
      | ~ r1_tarski(k1_relat_1(C_47),A_45)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_504,plain,(
    ! [C_106,A_107,B_108] :
      ( k7_relat_1(C_106,k4_xboole_0(A_107,B_108)) = k4_xboole_0(C_106,k7_relat_1(C_106,B_108))
      | ~ r1_tarski(k1_relat_1(C_106),A_107)
      | ~ v1_relat_1(C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_36])).

tff(c_516,plain,(
    ! [C_106,B_108] :
      ( k7_relat_1(C_106,k4_xboole_0(k1_relat_1(C_106),B_108)) = k4_xboole_0(C_106,k7_relat_1(C_106,B_108))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_8,c_504])).

tff(c_1779,plain,(
    ! [A_149] : k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2',A_149))) = k4_xboole_0(k1_relat_1('#skF_2'),A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_10])).

tff(c_1799,plain,(
    ! [B_108] :
      ( k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2',B_108)))) = k4_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),B_108))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_1779])).

tff(c_1859,plain,(
    ! [B_150] : k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2',B_150)))) = k1_relat_1(k7_relat_1('#skF_2',B_150)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1636,c_16,c_1799])).

tff(c_1902,plain,(
    ! [A_48] :
      ( k5_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),A_48)) = k1_relat_1(k7_relat_1('#skF_2',A_48))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_1859])).

tff(c_1922,plain,(
    ! [A_151] : k5_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),A_151)) = k1_relat_1(k7_relat_1('#skF_2',A_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1902])).

tff(c_1947,plain,(
    ! [B_69] : k5_xboole_0(k1_relat_1('#skF_2'),k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),B_69))) = k1_relat_1(k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),B_69))) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1922])).

tff(c_1969,plain,(
    ! [B_152] : k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2',B_152)))) = k1_relat_1(k7_relat_1('#skF_2',B_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_16,c_1677,c_1636,c_1636,c_1947])).

tff(c_231,plain,(
    ! [B_75,A_76] :
      ( k3_xboole_0(k1_relat_1(B_75),A_76) = k1_relat_1(k7_relat_1(B_75,A_76))
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_237,plain,(
    ! [B_75,A_76] :
      ( k5_xboole_0(k1_relat_1(B_75),k1_relat_1(k7_relat_1(B_75,A_76))) = k4_xboole_0(k1_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_10])).

tff(c_2001,plain,(
    ! [B_152] :
      ( k5_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2',B_152))) = k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2',B_152)))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1969,c_237])).

tff(c_2047,plain,(
    ! [B_152] : k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2',B_152))) = k4_xboole_0(k1_relat_1('#skF_2'),B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1677,c_2001])).

tff(c_1955,plain,(
    ! [B_10] : k5_xboole_0(k1_relat_1('#skF_2'),k3_xboole_0(k1_relat_1('#skF_2'),B_10)) = k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),B_10))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1922])).

tff(c_2063,plain,(
    ! [B_153] : k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),B_153))) = k4_xboole_0(k1_relat_1('#skF_2'),B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1955])).

tff(c_2119,plain,(
    ! [B_108] :
      ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2',B_108))) = k4_xboole_0(k1_relat_1('#skF_2'),B_108)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_2063])).

tff(c_2151,plain,(
    ! [B_108] : k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2',B_108))) = k4_xboole_0(k1_relat_1('#skF_2'),B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2119])).

tff(c_42,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_42])).

tff(c_2442,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2151,c_46])).

tff(c_2717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2047,c_2442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.79  
% 4.45/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.79  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.45/1.79  
% 4.45/1.79  %Foreground sorts:
% 4.45/1.79  
% 4.45/1.79  
% 4.45/1.79  %Background operators:
% 4.45/1.79  
% 4.45/1.79  
% 4.45/1.79  %Foreground operators:
% 4.45/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.45/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.45/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.45/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.45/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.45/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.79  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.45/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.45/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.45/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.45/1.79  
% 4.45/1.81  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 4.45/1.81  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.45/1.81  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.45/1.81  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.45/1.81  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.45/1.81  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 4.45/1.81  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 4.45/1.81  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 4.45/1.81  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.45/1.81  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.45/1.81  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 4.45/1.81  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.45/1.81  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.45/1.81  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.81  tff(c_164, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/1.81  tff(c_179, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_164])).
% 4.45/1.81  tff(c_182, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 4.45/1.81  tff(c_30, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.45/1.81  tff(c_34, plain, (![C_44, A_42, B_43]: (k6_subset_1(k7_relat_1(C_44, A_42), k7_relat_1(C_44, B_43))=k7_relat_1(C_44, k6_subset_1(A_42, B_43)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.45/1.81  tff(c_429, plain, (![C_102, A_103, B_104]: (k4_xboole_0(k7_relat_1(C_102, A_103), k7_relat_1(C_102, B_104))=k7_relat_1(C_102, k4_xboole_0(A_103, B_104)) | ~v1_relat_1(C_102))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_34])).
% 4.45/1.81  tff(c_439, plain, (![C_102, B_104]: (k7_relat_1(C_102, k4_xboole_0(B_104, B_104))=k1_xboole_0 | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_429, c_182])).
% 4.45/1.81  tff(c_455, plain, (![C_105]: (k7_relat_1(C_105, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_105))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_439])).
% 4.45/1.81  tff(c_459, plain, (k7_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_455])).
% 4.45/1.81  tff(c_38, plain, (![B_49, A_48]: (k1_relat_1(k6_subset_1(B_49, k7_relat_1(B_49, A_48)))=k6_subset_1(k1_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.45/1.81  tff(c_325, plain, (![B_85, A_86]: (k1_relat_1(k4_xboole_0(B_85, k7_relat_1(B_85, A_86)))=k4_xboole_0(k1_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_38])).
% 4.45/1.81  tff(c_40, plain, (![B_51, A_50]: (k3_xboole_0(k1_relat_1(B_51), A_50)=k1_relat_1(k7_relat_1(B_51, A_50)) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.45/1.81  tff(c_1547, plain, (![B_145, A_146, A_147]: (k1_relat_1(k7_relat_1(k4_xboole_0(B_145, k7_relat_1(B_145, A_146)), A_147))=k3_xboole_0(k4_xboole_0(k1_relat_1(B_145), A_146), A_147) | ~v1_relat_1(k4_xboole_0(B_145, k7_relat_1(B_145, A_146))) | ~v1_relat_1(B_145))), inference(superposition, [status(thm), theory('equality')], [c_325, c_40])).
% 4.45/1.81  tff(c_1616, plain, (![A_147]: (k3_xboole_0(k4_xboole_0(k1_relat_1('#skF_2'), k1_xboole_0), A_147)=k1_relat_1(k7_relat_1(k4_xboole_0('#skF_2', k1_xboole_0), A_147)) | ~v1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', k1_xboole_0))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_459, c_1547])).
% 4.45/1.81  tff(c_1638, plain, (![A_148]: (k3_xboole_0(k1_relat_1('#skF_2'), A_148)=k1_relat_1(k7_relat_1('#skF_2', A_148)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_14, c_459, c_14, c_14, c_1616])).
% 4.45/1.81  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.45/1.81  tff(c_1677, plain, (![A_148]: (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', A_148)))=k4_xboole_0(k1_relat_1('#skF_2'), A_148))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_10])).
% 4.45/1.81  tff(c_1636, plain, (![A_147]: (k3_xboole_0(k1_relat_1('#skF_2'), A_147)=k1_relat_1(k7_relat_1('#skF_2', A_147)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_14, c_459, c_14, c_14, c_1616])).
% 4.45/1.81  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/1.81  tff(c_167, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k3_xboole_0(A_68, k4_xboole_0(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_16])).
% 4.45/1.81  tff(c_45, plain, (![B_49, A_48]: (k1_relat_1(k4_xboole_0(B_49, k7_relat_1(B_49, A_48)))=k4_xboole_0(k1_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_38])).
% 4.45/1.81  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.45/1.81  tff(c_36, plain, (![C_47, A_45, B_46]: (k7_relat_1(C_47, k6_subset_1(A_45, B_46))=k6_subset_1(C_47, k7_relat_1(C_47, B_46)) | ~r1_tarski(k1_relat_1(C_47), A_45) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.45/1.81  tff(c_504, plain, (![C_106, A_107, B_108]: (k7_relat_1(C_106, k4_xboole_0(A_107, B_108))=k4_xboole_0(C_106, k7_relat_1(C_106, B_108)) | ~r1_tarski(k1_relat_1(C_106), A_107) | ~v1_relat_1(C_106))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_36])).
% 4.45/1.81  tff(c_516, plain, (![C_106, B_108]: (k7_relat_1(C_106, k4_xboole_0(k1_relat_1(C_106), B_108))=k4_xboole_0(C_106, k7_relat_1(C_106, B_108)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_8, c_504])).
% 4.45/1.81  tff(c_1779, plain, (![A_149]: (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', A_149)))=k4_xboole_0(k1_relat_1('#skF_2'), A_149))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_10])).
% 4.45/1.81  tff(c_1799, plain, (![B_108]: (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', B_108))))=k4_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), B_108)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_516, c_1779])).
% 4.45/1.81  tff(c_1859, plain, (![B_150]: (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', B_150))))=k1_relat_1(k7_relat_1('#skF_2', B_150)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1636, c_16, c_1799])).
% 4.45/1.81  tff(c_1902, plain, (![A_48]: (k5_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), A_48))=k1_relat_1(k7_relat_1('#skF_2', A_48)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_1859])).
% 4.45/1.81  tff(c_1922, plain, (![A_151]: (k5_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), A_151))=k1_relat_1(k7_relat_1('#skF_2', A_151)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1902])).
% 4.45/1.81  tff(c_1947, plain, (![B_69]: (k5_xboole_0(k1_relat_1('#skF_2'), k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), B_69)))=k1_relat_1(k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), B_69))))), inference(superposition, [status(thm), theory('equality')], [c_167, c_1922])).
% 4.45/1.81  tff(c_1969, plain, (![B_152]: (k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', B_152))))=k1_relat_1(k7_relat_1('#skF_2', B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_16, c_1677, c_1636, c_1636, c_1947])).
% 4.45/1.81  tff(c_231, plain, (![B_75, A_76]: (k3_xboole_0(k1_relat_1(B_75), A_76)=k1_relat_1(k7_relat_1(B_75, A_76)) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.45/1.81  tff(c_237, plain, (![B_75, A_76]: (k5_xboole_0(k1_relat_1(B_75), k1_relat_1(k7_relat_1(B_75, A_76)))=k4_xboole_0(k1_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(superposition, [status(thm), theory('equality')], [c_231, c_10])).
% 4.45/1.81  tff(c_2001, plain, (![B_152]: (k5_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', B_152)))=k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', B_152))) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1969, c_237])).
% 4.45/1.81  tff(c_2047, plain, (![B_152]: (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', B_152)))=k4_xboole_0(k1_relat_1('#skF_2'), B_152))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1677, c_2001])).
% 4.45/1.81  tff(c_1955, plain, (![B_10]: (k5_xboole_0(k1_relat_1('#skF_2'), k3_xboole_0(k1_relat_1('#skF_2'), B_10))=k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), B_10))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1922])).
% 4.45/1.81  tff(c_2063, plain, (![B_153]: (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), B_153)))=k4_xboole_0(k1_relat_1('#skF_2'), B_153))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1955])).
% 4.45/1.81  tff(c_2119, plain, (![B_108]: (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', B_108)))=k4_xboole_0(k1_relat_1('#skF_2'), B_108) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_516, c_2063])).
% 4.45/1.81  tff(c_2151, plain, (![B_108]: (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', B_108)))=k4_xboole_0(k1_relat_1('#skF_2'), B_108))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2119])).
% 4.45/1.81  tff(c_42, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.45/1.81  tff(c_46, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_42])).
% 4.45/1.81  tff(c_2442, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2151, c_46])).
% 4.45/1.81  tff(c_2717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2047, c_2442])).
% 4.45/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.81  
% 4.45/1.81  Inference rules
% 4.45/1.81  ----------------------
% 4.45/1.81  #Ref     : 0
% 4.45/1.81  #Sup     : 657
% 4.45/1.81  #Fact    : 0
% 4.45/1.81  #Define  : 0
% 4.45/1.81  #Split   : 1
% 4.45/1.81  #Chain   : 0
% 4.45/1.81  #Close   : 0
% 4.45/1.81  
% 4.45/1.81  Ordering : KBO
% 4.45/1.81  
% 4.45/1.81  Simplification rules
% 4.45/1.81  ----------------------
% 4.45/1.81  #Subsume      : 29
% 4.45/1.81  #Demod        : 687
% 4.45/1.81  #Tautology    : 267
% 4.45/1.81  #SimpNegUnit  : 0
% 4.45/1.81  #BackRed      : 3
% 4.45/1.81  
% 4.45/1.81  #Partial instantiations: 0
% 4.45/1.81  #Strategies tried      : 1
% 4.45/1.81  
% 4.45/1.81  Timing (in seconds)
% 4.45/1.81  ----------------------
% 4.45/1.81  Preprocessing        : 0.32
% 4.45/1.81  Parsing              : 0.17
% 4.45/1.81  CNF conversion       : 0.02
% 4.45/1.81  Main loop            : 0.73
% 4.45/1.81  Inferencing          : 0.25
% 4.45/1.81  Reduction            : 0.28
% 4.45/1.81  Demodulation         : 0.22
% 4.45/1.81  BG Simplification    : 0.04
% 4.45/1.81  Subsumption          : 0.13
% 4.45/1.81  Abstraction          : 0.06
% 4.45/1.81  MUC search           : 0.00
% 4.45/1.81  Cooper               : 0.00
% 4.45/1.81  Total                : 1.08
% 4.45/1.81  Index Insertion      : 0.00
% 4.45/1.81  Index Deletion       : 0.00
% 4.45/1.81  Index Matching       : 0.00
% 4.45/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
