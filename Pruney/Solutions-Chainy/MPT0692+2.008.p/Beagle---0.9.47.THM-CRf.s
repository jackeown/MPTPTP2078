%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:50 EST 2020

% Result     : Theorem 13.12s
% Output     : CNFRefutation 13.15s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 125 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 224 expanded)
%              Number of equality atoms :   50 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(A,k2_relat_1(B))
         => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_42,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_280,plain,(
    ! [B_69,A_70] :
      ( k10_relat_1(B_69,A_70) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2393,plain,(
    ! [B_149,B_150] :
      ( k10_relat_1(B_149,B_150) = k1_xboole_0
      | ~ v1_relat_1(B_149)
      | k4_xboole_0(k2_relat_1(B_149),B_150) != k2_relat_1(B_149) ) ),
    inference(resolution,[status(thm)],[c_16,c_280])).

tff(c_2443,plain,(
    ! [B_151] :
      ( k10_relat_1(B_151,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2393])).

tff(c_2447,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_2443])).

tff(c_28,plain,(
    ! [A_26] :
      ( k10_relat_1(A_26,k2_relat_1(A_26)) = k1_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_22,B_23] : k6_subset_1(A_22,B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [C_33,A_31,B_32] :
      ( k6_subset_1(k10_relat_1(C_33,A_31),k10_relat_1(C_33,B_32)) = k10_relat_1(C_33,k6_subset_1(A_31,B_32))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1686,plain,(
    ! [C_127,A_128,B_129] :
      ( k4_xboole_0(k10_relat_1(C_127,A_128),k10_relat_1(C_127,B_129)) = k10_relat_1(C_127,k4_xboole_0(A_128,B_129))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_36])).

tff(c_3204,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(k1_relat_1(A_166),k10_relat_1(A_166,B_167)) = k10_relat_1(A_166,k4_xboole_0(k2_relat_1(A_166),B_167))
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1686])).

tff(c_3235,plain,
    ( k10_relat_1('#skF_2',k4_xboole_0(k2_relat_1('#skF_2'),k1_xboole_0)) = k4_xboole_0(k1_relat_1('#skF_2'),k1_xboole_0)
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2447,c_3204])).

tff(c_3250,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_46,c_8,c_8,c_3235])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k10_relat_1(B_28,A_27),k10_relat_1(B_28,k2_relat_1(B_28)))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3306,plain,(
    ! [A_27] :
      ( r1_tarski(k10_relat_1('#skF_2',A_27),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3250,c_30])).

tff(c_3343,plain,(
    ! [A_27] : r1_tarski(k10_relat_1('#skF_2',A_27),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3306])).

tff(c_655,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(A_97,k10_relat_1(B_98,k9_relat_1(B_98,A_97)))
      | ~ r1_tarski(A_97,k1_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2892,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(A_159,k10_relat_1(B_160,k9_relat_1(B_160,A_159))) = k1_xboole_0
      | ~ r1_tarski(A_159,k1_relat_1(B_160))
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_655,c_6])).

tff(c_49,plain,(
    ! [C_33,A_31,B_32] :
      ( k4_xboole_0(k10_relat_1(C_33,A_31),k10_relat_1(C_33,B_32)) = k10_relat_1(C_33,k4_xboole_0(A_31,B_32))
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_36])).

tff(c_31035,plain,(
    ! [B_469,A_470] :
      ( k10_relat_1(B_469,k4_xboole_0(A_470,k9_relat_1(B_469,k10_relat_1(B_469,A_470)))) = k1_xboole_0
      | ~ v1_funct_1(B_469)
      | ~ v1_relat_1(B_469)
      | ~ r1_tarski(k10_relat_1(B_469,A_470),k1_relat_1(B_469))
      | ~ v1_relat_1(B_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2892,c_49])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_286,plain,(
    ! [B_71,A_72] :
      ( r1_xboole_0(k2_relat_1(B_71),A_72)
      | k10_relat_1(B_71,A_72) != k1_xboole_0
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2126,plain,(
    ! [B_145,A_146] :
      ( k4_xboole_0(k2_relat_1(B_145),A_146) = k2_relat_1(B_145)
      | k10_relat_1(B_145,A_146) != k1_xboole_0
      | ~ v1_relat_1(B_145) ) ),
    inference(resolution,[status(thm)],[c_286,c_14])).

tff(c_44,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_265,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_xboole_0(A_64,C_65)
      | ~ r1_xboole_0(B_66,C_65)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_353,plain,(
    ! [A_79,B_80,A_81] :
      ( r1_xboole_0(A_79,B_80)
      | ~ r1_tarski(A_79,A_81)
      | k4_xboole_0(A_81,B_80) != A_81 ) ),
    inference(resolution,[status(thm)],[c_16,c_265])).

tff(c_362,plain,(
    ! [B_80] :
      ( r1_xboole_0('#skF_1',B_80)
      | k4_xboole_0(k2_relat_1('#skF_2'),B_80) != k2_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_353])).

tff(c_2161,plain,(
    ! [A_146] :
      ( r1_xboole_0('#skF_1',A_146)
      | k10_relat_1('#skF_2',A_146) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2126,c_362])).

tff(c_2254,plain,(
    ! [A_147] :
      ( r1_xboole_0('#skF_1',A_147)
      | k10_relat_1('#skF_2',A_147) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2161])).

tff(c_2262,plain,(
    ! [A_148] :
      ( k4_xboole_0('#skF_1',A_148) = '#skF_1'
      | k10_relat_1('#skF_2',A_148) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2254,c_14])).

tff(c_2362,plain,(
    ! [B_7] :
      ( k3_xboole_0('#skF_1',B_7) = '#skF_1'
      | k10_relat_1('#skF_2',k4_xboole_0('#skF_1',B_7)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2262])).

tff(c_31188,plain,
    ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_2','#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31035,c_2362])).

tff(c_31415,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3343,c_46,c_31188])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_413,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(k9_relat_1(B_84,k10_relat_1(B_84,A_85)),A_85)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2573,plain,(
    ! [B_152,A_153] :
      ( k4_xboole_0(k9_relat_1(B_152,k10_relat_1(B_152,A_153)),A_153) = k1_xboole_0
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_413,c_6])).

tff(c_2583,plain,(
    ! [B_152,A_153] :
      ( k4_xboole_0(k9_relat_1(B_152,k10_relat_1(B_152,A_153)),k1_xboole_0) = k3_xboole_0(k9_relat_1(B_152,k10_relat_1(B_152,A_153)),A_153)
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2573,c_10])).

tff(c_2606,plain,(
    ! [A_153,B_152] :
      ( k3_xboole_0(A_153,k9_relat_1(B_152,k10_relat_1(B_152,A_153))) = k9_relat_1(B_152,k10_relat_1(B_152,A_153))
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_2583])).

tff(c_31477,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31415,c_2606])).

tff(c_31507,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_31477])).

tff(c_31509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_31507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:34:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.12/5.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.43  
% 13.15/5.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.44  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 13.15/5.44  
% 13.15/5.44  %Foreground sorts:
% 13.15/5.44  
% 13.15/5.44  
% 13.15/5.44  %Background operators:
% 13.15/5.44  
% 13.15/5.44  
% 13.15/5.44  %Foreground operators:
% 13.15/5.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.15/5.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.15/5.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.15/5.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.15/5.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.15/5.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.15/5.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.15/5.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.15/5.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.15/5.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.15/5.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.15/5.44  tff('#skF_2', type, '#skF_2': $i).
% 13.15/5.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.15/5.44  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.15/5.44  tff('#skF_1', type, '#skF_1': $i).
% 13.15/5.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.15/5.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.15/5.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.15/5.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.15/5.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.15/5.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.15/5.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.15/5.44  
% 13.15/5.45  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 13.15/5.45  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 13.15/5.45  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.15/5.45  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 13.15/5.45  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 13.15/5.45  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.15/5.45  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 13.15/5.45  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 13.15/5.45  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 13.15/5.45  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.15/5.45  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.15/5.45  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 13.15/5.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.15/5.45  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 13.15/5.45  tff(c_42, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.15/5.45  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.15/5.45  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.15/5.45  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.15/5.45  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.15/5.45  tff(c_280, plain, (![B_69, A_70]: (k10_relat_1(B_69, A_70)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.15/5.45  tff(c_2393, plain, (![B_149, B_150]: (k10_relat_1(B_149, B_150)=k1_xboole_0 | ~v1_relat_1(B_149) | k4_xboole_0(k2_relat_1(B_149), B_150)!=k2_relat_1(B_149))), inference(resolution, [status(thm)], [c_16, c_280])).
% 13.15/5.45  tff(c_2443, plain, (![B_151]: (k10_relat_1(B_151, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_151))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2393])).
% 13.15/5.45  tff(c_2447, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_2443])).
% 13.15/5.45  tff(c_28, plain, (![A_26]: (k10_relat_1(A_26, k2_relat_1(A_26))=k1_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.15/5.45  tff(c_24, plain, (![A_22, B_23]: (k6_subset_1(A_22, B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.15/5.45  tff(c_36, plain, (![C_33, A_31, B_32]: (k6_subset_1(k10_relat_1(C_33, A_31), k10_relat_1(C_33, B_32))=k10_relat_1(C_33, k6_subset_1(A_31, B_32)) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.15/5.45  tff(c_1686, plain, (![C_127, A_128, B_129]: (k4_xboole_0(k10_relat_1(C_127, A_128), k10_relat_1(C_127, B_129))=k10_relat_1(C_127, k4_xboole_0(A_128, B_129)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_36])).
% 13.15/5.45  tff(c_3204, plain, (![A_166, B_167]: (k4_xboole_0(k1_relat_1(A_166), k10_relat_1(A_166, B_167))=k10_relat_1(A_166, k4_xboole_0(k2_relat_1(A_166), B_167)) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1686])).
% 13.15/5.45  tff(c_3235, plain, (k10_relat_1('#skF_2', k4_xboole_0(k2_relat_1('#skF_2'), k1_xboole_0))=k4_xboole_0(k1_relat_1('#skF_2'), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2447, c_3204])).
% 13.15/5.45  tff(c_3250, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_46, c_8, c_8, c_3235])).
% 13.15/5.45  tff(c_30, plain, (![B_28, A_27]: (r1_tarski(k10_relat_1(B_28, A_27), k10_relat_1(B_28, k2_relat_1(B_28))) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.15/5.45  tff(c_3306, plain, (![A_27]: (r1_tarski(k10_relat_1('#skF_2', A_27), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3250, c_30])).
% 13.15/5.45  tff(c_3343, plain, (![A_27]: (r1_tarski(k10_relat_1('#skF_2', A_27), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3306])).
% 13.15/5.45  tff(c_655, plain, (![A_97, B_98]: (r1_tarski(A_97, k10_relat_1(B_98, k9_relat_1(B_98, A_97))) | ~r1_tarski(A_97, k1_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.15/5.45  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.15/5.45  tff(c_2892, plain, (![A_159, B_160]: (k4_xboole_0(A_159, k10_relat_1(B_160, k9_relat_1(B_160, A_159)))=k1_xboole_0 | ~r1_tarski(A_159, k1_relat_1(B_160)) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_655, c_6])).
% 13.15/5.45  tff(c_49, plain, (![C_33, A_31, B_32]: (k4_xboole_0(k10_relat_1(C_33, A_31), k10_relat_1(C_33, B_32))=k10_relat_1(C_33, k4_xboole_0(A_31, B_32)) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_36])).
% 13.15/5.45  tff(c_31035, plain, (![B_469, A_470]: (k10_relat_1(B_469, k4_xboole_0(A_470, k9_relat_1(B_469, k10_relat_1(B_469, A_470))))=k1_xboole_0 | ~v1_funct_1(B_469) | ~v1_relat_1(B_469) | ~r1_tarski(k10_relat_1(B_469, A_470), k1_relat_1(B_469)) | ~v1_relat_1(B_469))), inference(superposition, [status(thm), theory('equality')], [c_2892, c_49])).
% 13.15/5.45  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.15/5.45  tff(c_286, plain, (![B_71, A_72]: (r1_xboole_0(k2_relat_1(B_71), A_72) | k10_relat_1(B_71, A_72)!=k1_xboole_0 | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.15/5.45  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.15/5.45  tff(c_2126, plain, (![B_145, A_146]: (k4_xboole_0(k2_relat_1(B_145), A_146)=k2_relat_1(B_145) | k10_relat_1(B_145, A_146)!=k1_xboole_0 | ~v1_relat_1(B_145))), inference(resolution, [status(thm)], [c_286, c_14])).
% 13.15/5.45  tff(c_44, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.15/5.45  tff(c_265, plain, (![A_64, C_65, B_66]: (r1_xboole_0(A_64, C_65) | ~r1_xboole_0(B_66, C_65) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.15/5.45  tff(c_353, plain, (![A_79, B_80, A_81]: (r1_xboole_0(A_79, B_80) | ~r1_tarski(A_79, A_81) | k4_xboole_0(A_81, B_80)!=A_81)), inference(resolution, [status(thm)], [c_16, c_265])).
% 13.15/5.45  tff(c_362, plain, (![B_80]: (r1_xboole_0('#skF_1', B_80) | k4_xboole_0(k2_relat_1('#skF_2'), B_80)!=k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_353])).
% 13.15/5.45  tff(c_2161, plain, (![A_146]: (r1_xboole_0('#skF_1', A_146) | k10_relat_1('#skF_2', A_146)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2126, c_362])).
% 13.15/5.45  tff(c_2254, plain, (![A_147]: (r1_xboole_0('#skF_1', A_147) | k10_relat_1('#skF_2', A_147)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2161])).
% 13.15/5.45  tff(c_2262, plain, (![A_148]: (k4_xboole_0('#skF_1', A_148)='#skF_1' | k10_relat_1('#skF_2', A_148)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2254, c_14])).
% 13.15/5.45  tff(c_2362, plain, (![B_7]: (k3_xboole_0('#skF_1', B_7)='#skF_1' | k10_relat_1('#skF_2', k4_xboole_0('#skF_1', B_7))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_2262])).
% 13.15/5.45  tff(c_31188, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~v1_funct_1('#skF_2') | ~r1_tarski(k10_relat_1('#skF_2', '#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31035, c_2362])).
% 13.15/5.45  tff(c_31415, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3343, c_46, c_31188])).
% 13.15/5.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.15/5.45  tff(c_413, plain, (![B_84, A_85]: (r1_tarski(k9_relat_1(B_84, k10_relat_1(B_84, A_85)), A_85) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.15/5.45  tff(c_2573, plain, (![B_152, A_153]: (k4_xboole_0(k9_relat_1(B_152, k10_relat_1(B_152, A_153)), A_153)=k1_xboole_0 | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_413, c_6])).
% 13.15/5.45  tff(c_2583, plain, (![B_152, A_153]: (k4_xboole_0(k9_relat_1(B_152, k10_relat_1(B_152, A_153)), k1_xboole_0)=k3_xboole_0(k9_relat_1(B_152, k10_relat_1(B_152, A_153)), A_153) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(superposition, [status(thm), theory('equality')], [c_2573, c_10])).
% 13.15/5.45  tff(c_2606, plain, (![A_153, B_152]: (k3_xboole_0(A_153, k9_relat_1(B_152, k10_relat_1(B_152, A_153)))=k9_relat_1(B_152, k10_relat_1(B_152, A_153)) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_2583])).
% 13.15/5.45  tff(c_31477, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31415, c_2606])).
% 13.15/5.45  tff(c_31507, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_31477])).
% 13.15/5.45  tff(c_31509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_31507])).
% 13.15/5.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.15/5.45  
% 13.15/5.45  Inference rules
% 13.15/5.45  ----------------------
% 13.15/5.45  #Ref     : 0
% 13.15/5.45  #Sup     : 7109
% 13.15/5.45  #Fact    : 0
% 13.15/5.45  #Define  : 0
% 13.15/5.45  #Split   : 16
% 13.15/5.45  #Chain   : 0
% 13.15/5.45  #Close   : 0
% 13.15/5.45  
% 13.15/5.45  Ordering : KBO
% 13.15/5.45  
% 13.15/5.45  Simplification rules
% 13.15/5.45  ----------------------
% 13.15/5.45  #Subsume      : 1944
% 13.15/5.45  #Demod        : 11977
% 13.15/5.45  #Tautology    : 2764
% 13.15/5.45  #SimpNegUnit  : 216
% 13.15/5.45  #BackRed      : 43
% 13.15/5.45  
% 13.15/5.45  #Partial instantiations: 0
% 13.15/5.45  #Strategies tried      : 1
% 13.15/5.45  
% 13.15/5.45  Timing (in seconds)
% 13.15/5.45  ----------------------
% 13.15/5.45  Preprocessing        : 0.31
% 13.15/5.45  Parsing              : 0.17
% 13.15/5.45  CNF conversion       : 0.02
% 13.15/5.45  Main loop            : 4.37
% 13.15/5.45  Inferencing          : 0.94
% 13.15/5.45  Reduction            : 2.18
% 13.15/5.45  Demodulation         : 1.81
% 13.15/5.45  BG Simplification    : 0.09
% 13.15/5.46  Subsumption          : 0.95
% 13.15/5.46  Abstraction          : 0.15
% 13.15/5.46  MUC search           : 0.00
% 13.15/5.46  Cooper               : 0.00
% 13.15/5.46  Total                : 4.72
% 13.15/5.46  Index Insertion      : 0.00
% 13.15/5.46  Index Deletion       : 0.00
% 13.15/5.46  Index Matching       : 0.00
% 13.15/5.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
