%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 180 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 285 expanded)
%              Number of equality atoms :   29 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k4_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = A_45
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_91,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_47] : r1_tarski(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_6])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,'#skF_2')
      | ~ r1_tarski(A_54,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_421,plain,(
    ! [A_72,A_73] :
      ( r1_tarski(A_72,'#skF_2')
      | ~ r1_tarski(A_72,A_73)
      | ~ r1_tarski(A_73,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_177,c_4])).

tff(c_435,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k4_xboole_0(A_6,B_7),'#skF_2')
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_421])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [B_12,A_11] : r1_xboole_0(B_12,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_12,c_38])).

tff(c_181,plain,(
    ! [B_55,A_56] : k4_xboole_0(B_55,k4_xboole_0(A_56,B_55)) = B_55 ),
    inference(resolution,[status(thm)],[c_43,c_70])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1840,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0(A_141,B_142) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_141,B_142),B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_8])).

tff(c_2097,plain,(
    ! [A_145] :
      ( k4_xboole_0(A_145,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_145,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_435,c_1840])).

tff(c_2117,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_2097])).

tff(c_496,plain,(
    ! [B_80,A_81,C_82] :
      ( r1_xboole_0(B_80,k4_xboole_0(A_81,C_82))
      | ~ r1_xboole_0(A_81,k4_xboole_0(B_80,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_527,plain,(
    ! [B_80,A_11,C_82] : r1_xboole_0(B_80,k4_xboole_0(k4_xboole_0(A_11,k4_xboole_0(B_80,C_82)),C_82)) ),
    inference(resolution,[status(thm)],[c_12,c_496])).

tff(c_2155,plain,(
    ! [A_11] : r1_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0(A_11,k1_xboole_0),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_527])).

tff(c_2213,plain,(
    ! [A_11] : r1_xboole_0('#skF_1',k4_xboole_0(A_11,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2155])).

tff(c_44,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_10,c_38])).

tff(c_370,plain,(
    ! [A_67,B_68] :
      ( k7_relat_1(A_67,B_68) = k1_xboole_0
      | ~ r1_xboole_0(B_68,k1_relat_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_391,plain,(
    ! [A_69] :
      ( k7_relat_1(A_69,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_44,c_370])).

tff(c_399,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_391])).

tff(c_26,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(k6_subset_1(B_26,k7_relat_1(B_26,A_25))) = k6_subset_1(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    ! [B_26,A_25] :
      ( k1_relat_1(k4_xboole_0(B_26,k7_relat_1(B_26,A_25))) = k4_xboole_0(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_26])).

tff(c_1103,plain,(
    ! [B_103,A_104] :
      ( k1_relat_1(k4_xboole_0(B_103,k7_relat_1(B_103,A_104))) = k4_xboole_0(k1_relat_1(B_103),A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_26])).

tff(c_24,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1618,plain,(
    ! [B_129,A_130,B_131] :
      ( k7_relat_1(k4_xboole_0(B_129,k7_relat_1(B_129,A_130)),B_131) = k1_xboole_0
      | ~ r1_xboole_0(B_131,k4_xboole_0(k1_relat_1(B_129),A_130))
      | ~ v1_relat_1(k4_xboole_0(B_129,k7_relat_1(B_129,A_130)))
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_24])).

tff(c_14256,plain,(
    ! [B_339,A_340,A_341,B_342] :
      ( k7_relat_1(k4_xboole_0(k4_xboole_0(B_339,k7_relat_1(B_339,A_340)),k7_relat_1(k4_xboole_0(B_339,k7_relat_1(B_339,A_340)),A_341)),B_342) = k1_xboole_0
      | ~ r1_xboole_0(B_342,k4_xboole_0(k4_xboole_0(k1_relat_1(B_339),A_340),A_341))
      | ~ v1_relat_1(k4_xboole_0(k4_xboole_0(B_339,k7_relat_1(B_339,A_340)),k7_relat_1(k4_xboole_0(B_339,k7_relat_1(B_339,A_340)),A_341)))
      | ~ v1_relat_1(k4_xboole_0(B_339,k7_relat_1(B_339,A_340)))
      | ~ v1_relat_1(B_339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_1618])).

tff(c_14312,plain,(
    ! [A_341,B_342] :
      ( k7_relat_1(k4_xboole_0(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',k1_xboole_0)),k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',k1_xboole_0)),A_341)),B_342) = k1_xboole_0
      | ~ r1_xboole_0(B_342,k4_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'),k1_xboole_0),A_341))
      | ~ v1_relat_1(k4_xboole_0(k4_xboole_0('#skF_3',k1_xboole_0),k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',k1_xboole_0)),A_341)))
      | ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',k1_xboole_0)))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_14256])).

tff(c_14652,plain,(
    ! [A_348,B_349] :
      ( k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',A_348)),B_349) = k1_xboole_0
      | ~ r1_xboole_0(B_349,k4_xboole_0(k1_relat_1('#skF_3'),A_348))
      | ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',A_348))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_90,c_399,c_90,c_90,c_399,c_90,c_90,c_90,c_399,c_399,c_14312])).

tff(c_14752,plain,
    ( k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') = k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2213,c_14652])).

tff(c_14822,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_14752])).

tff(c_14840,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_14822])).

tff(c_14844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.68  
% 7.31/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.68  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.31/2.68  
% 7.31/2.68  %Foreground sorts:
% 7.31/2.68  
% 7.31/2.68  
% 7.31/2.68  %Background operators:
% 7.31/2.68  
% 7.31/2.68  
% 7.31/2.68  %Foreground operators:
% 7.31/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.31/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.31/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.68  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.31/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.31/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.31/2.68  
% 7.31/2.70  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 7.31/2.70  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 7.31/2.70  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.31/2.70  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.31/2.70  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.31/2.70  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.31/2.70  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.31/2.70  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.31/2.70  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.31/2.70  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 7.31/2.70  tff(f_49, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 7.31/2.70  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 7.31/2.70  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 7.31/2.70  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.31/2.70  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k4_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.31/2.70  tff(c_20, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.31/2.70  tff(c_28, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.31/2.70  tff(c_34, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28])).
% 7.31/2.70  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.70  tff(c_70, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=A_45 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.31/2.70  tff(c_90, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(resolution, [status(thm)], [c_10, c_70])).
% 7.31/2.70  tff(c_91, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=A_47)), inference(resolution, [status(thm)], [c_10, c_70])).
% 7.31/2.70  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.70  tff(c_106, plain, (![A_47]: (r1_tarski(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_91, c_6])).
% 7.31/2.70  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.31/2.70  tff(c_118, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.70  tff(c_177, plain, (![A_54]: (r1_tarski(A_54, '#skF_2') | ~r1_tarski(A_54, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_118])).
% 7.31/2.70  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.70  tff(c_421, plain, (![A_72, A_73]: (r1_tarski(A_72, '#skF_2') | ~r1_tarski(A_72, A_73) | ~r1_tarski(A_73, '#skF_1'))), inference(resolution, [status(thm)], [c_177, c_4])).
% 7.31/2.70  tff(c_435, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), '#skF_2') | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_421])).
% 7.31/2.70  tff(c_12, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.70  tff(c_38, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.31/2.70  tff(c_43, plain, (![B_12, A_11]: (r1_xboole_0(B_12, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_12, c_38])).
% 7.31/2.70  tff(c_181, plain, (![B_55, A_56]: (k4_xboole_0(B_55, k4_xboole_0(A_56, B_55))=B_55)), inference(resolution, [status(thm)], [c_43, c_70])).
% 7.31/2.70  tff(c_8, plain, (![A_8, B_9]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k4_xboole_0(B_9, A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.71  tff(c_1840, plain, (![A_141, B_142]: (k4_xboole_0(A_141, B_142)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_141, B_142), B_142))), inference(superposition, [status(thm), theory('equality')], [c_181, c_8])).
% 7.31/2.71  tff(c_2097, plain, (![A_145]: (k4_xboole_0(A_145, '#skF_2')=k1_xboole_0 | ~r1_tarski(A_145, '#skF_1'))), inference(resolution, [status(thm)], [c_435, c_1840])).
% 7.31/2.71  tff(c_2117, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_2097])).
% 7.31/2.71  tff(c_496, plain, (![B_80, A_81, C_82]: (r1_xboole_0(B_80, k4_xboole_0(A_81, C_82)) | ~r1_xboole_0(A_81, k4_xboole_0(B_80, C_82)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.71  tff(c_527, plain, (![B_80, A_11, C_82]: (r1_xboole_0(B_80, k4_xboole_0(k4_xboole_0(A_11, k4_xboole_0(B_80, C_82)), C_82)))), inference(resolution, [status(thm)], [c_12, c_496])).
% 7.31/2.71  tff(c_2155, plain, (![A_11]: (r1_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0(A_11, k1_xboole_0), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2117, c_527])).
% 7.31/2.71  tff(c_2213, plain, (![A_11]: (r1_xboole_0('#skF_1', k4_xboole_0(A_11, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2155])).
% 7.31/2.71  tff(c_44, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_10, c_38])).
% 7.31/2.71  tff(c_370, plain, (![A_67, B_68]: (k7_relat_1(A_67, B_68)=k1_xboole_0 | ~r1_xboole_0(B_68, k1_relat_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.31/2.71  tff(c_391, plain, (![A_69]: (k7_relat_1(A_69, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_44, c_370])).
% 7.31/2.71  tff(c_399, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_391])).
% 7.31/2.71  tff(c_26, plain, (![B_26, A_25]: (k1_relat_1(k6_subset_1(B_26, k7_relat_1(B_26, A_25)))=k6_subset_1(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.71  tff(c_33, plain, (![B_26, A_25]: (k1_relat_1(k4_xboole_0(B_26, k7_relat_1(B_26, A_25)))=k4_xboole_0(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_26])).
% 7.31/2.71  tff(c_1103, plain, (![B_103, A_104]: (k1_relat_1(k4_xboole_0(B_103, k7_relat_1(B_103, A_104)))=k4_xboole_0(k1_relat_1(B_103), A_104) | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_26])).
% 7.31/2.71  tff(c_24, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.31/2.71  tff(c_1618, plain, (![B_129, A_130, B_131]: (k7_relat_1(k4_xboole_0(B_129, k7_relat_1(B_129, A_130)), B_131)=k1_xboole_0 | ~r1_xboole_0(B_131, k4_xboole_0(k1_relat_1(B_129), A_130)) | ~v1_relat_1(k4_xboole_0(B_129, k7_relat_1(B_129, A_130))) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_24])).
% 7.31/2.71  tff(c_14256, plain, (![B_339, A_340, A_341, B_342]: (k7_relat_1(k4_xboole_0(k4_xboole_0(B_339, k7_relat_1(B_339, A_340)), k7_relat_1(k4_xboole_0(B_339, k7_relat_1(B_339, A_340)), A_341)), B_342)=k1_xboole_0 | ~r1_xboole_0(B_342, k4_xboole_0(k4_xboole_0(k1_relat_1(B_339), A_340), A_341)) | ~v1_relat_1(k4_xboole_0(k4_xboole_0(B_339, k7_relat_1(B_339, A_340)), k7_relat_1(k4_xboole_0(B_339, k7_relat_1(B_339, A_340)), A_341))) | ~v1_relat_1(k4_xboole_0(B_339, k7_relat_1(B_339, A_340))) | ~v1_relat_1(B_339))), inference(superposition, [status(thm), theory('equality')], [c_33, c_1618])).
% 7.31/2.71  tff(c_14312, plain, (![A_341, B_342]: (k7_relat_1(k4_xboole_0(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', k1_xboole_0)), k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', k1_xboole_0)), A_341)), B_342)=k1_xboole_0 | ~r1_xboole_0(B_342, k4_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'), k1_xboole_0), A_341)) | ~v1_relat_1(k4_xboole_0(k4_xboole_0('#skF_3', k1_xboole_0), k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', k1_xboole_0)), A_341))) | ~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', k1_xboole_0))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_14256])).
% 7.31/2.71  tff(c_14652, plain, (![A_348, B_349]: (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', A_348)), B_349)=k1_xboole_0 | ~r1_xboole_0(B_349, k4_xboole_0(k1_relat_1('#skF_3'), A_348)) | ~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', A_348))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_90, c_399, c_90, c_90, c_399, c_90, c_90, c_90, c_399, c_399, c_14312])).
% 7.31/2.71  tff(c_14752, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_2213, c_14652])).
% 7.31/2.71  tff(c_14822, plain, (~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_14752])).
% 7.31/2.71  tff(c_14840, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_14822])).
% 7.31/2.71  tff(c_14844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_14840])).
% 7.31/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.71  
% 7.31/2.71  Inference rules
% 7.31/2.71  ----------------------
% 7.31/2.71  #Ref     : 0
% 7.31/2.71  #Sup     : 3575
% 7.31/2.71  #Fact    : 0
% 7.31/2.71  #Define  : 0
% 7.31/2.71  #Split   : 4
% 7.31/2.71  #Chain   : 0
% 7.31/2.71  #Close   : 0
% 7.31/2.71  
% 7.31/2.71  Ordering : KBO
% 7.31/2.71  
% 7.31/2.71  Simplification rules
% 7.31/2.71  ----------------------
% 7.31/2.71  #Subsume      : 604
% 7.31/2.71  #Demod        : 3863
% 7.31/2.71  #Tautology    : 2357
% 7.31/2.71  #SimpNegUnit  : 7
% 7.31/2.71  #BackRed      : 9
% 7.31/2.71  
% 7.31/2.71  #Partial instantiations: 0
% 7.31/2.71  #Strategies tried      : 1
% 7.31/2.71  
% 7.31/2.71  Timing (in seconds)
% 7.31/2.71  ----------------------
% 7.48/2.71  Preprocessing        : 0.29
% 7.48/2.71  Parsing              : 0.15
% 7.48/2.71  CNF conversion       : 0.02
% 7.48/2.71  Main loop            : 1.64
% 7.48/2.71  Inferencing          : 0.44
% 7.48/2.71  Reduction            : 0.73
% 7.48/2.71  Demodulation         : 0.59
% 7.48/2.71  BG Simplification    : 0.04
% 7.48/2.71  Subsumption          : 0.33
% 7.48/2.71  Abstraction          : 0.07
% 7.48/2.71  MUC search           : 0.00
% 7.48/2.71  Cooper               : 0.00
% 7.48/2.71  Total                : 1.97
% 7.48/2.71  Index Insertion      : 0.00
% 7.48/2.71  Index Deletion       : 0.00
% 7.48/2.71  Index Matching       : 0.00
% 7.48/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
