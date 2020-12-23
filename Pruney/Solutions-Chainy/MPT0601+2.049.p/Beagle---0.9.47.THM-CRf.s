%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:20 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   76 (  89 expanded)
%              Number of leaves         :   40 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 111 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_96,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_99,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_96])).

tff(c_337,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = k4_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_337])).

tff(c_349,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_346])).

tff(c_26,plain,(
    ! [B_31] : k4_xboole_0(k1_tarski(B_31),k1_tarski(B_31)) != k1_tarski(B_31) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_350,plain,(
    ! [B_31] : k1_tarski(B_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_26])).

tff(c_317,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_tarski(A_106),B_107)
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_322,plain,(
    ! [A_106] :
      ( k1_tarski(A_106) = k1_xboole_0
      | ~ r2_hidden(A_106,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_317,c_6])).

tff(c_358,plain,(
    ! [A_106] : ~ r2_hidden(A_106,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_322])).

tff(c_58,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_109,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    ! [A_93,B_94,C_95] :
      ( r2_hidden(k4_tarski(A_93,B_94),C_95)
      | ~ r2_hidden(B_94,k11_relat_1(C_95,A_93))
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [C_50,A_35,D_53] :
      ( r2_hidden(C_50,k1_relat_1(A_35))
      | ~ r2_hidden(k4_tarski(C_50,D_53),A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_225,plain,(
    ! [A_96,C_97,B_98] :
      ( r2_hidden(A_96,k1_relat_1(C_97))
      | ~ r2_hidden(B_98,k11_relat_1(C_97,A_96))
      | ~ v1_relat_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_210,c_36])).

tff(c_280,plain,(
    ! [A_102,C_103] :
      ( r2_hidden(A_102,k1_relat_1(C_103))
      | ~ v1_relat_1(C_103)
      | k11_relat_1(C_103,A_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_225])).

tff(c_52,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_167,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_52])).

tff(c_291,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_167])).

tff(c_299,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_291])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_299])).

tff(c_302,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_303,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_463,plain,(
    ! [C_146,A_147] :
      ( r2_hidden(k4_tarski(C_146,'#skF_5'(A_147,k1_relat_1(A_147),C_146)),A_147)
      | ~ r2_hidden(C_146,k1_relat_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [B_55,C_56,A_54] :
      ( r2_hidden(B_55,k11_relat_1(C_56,A_54))
      | ~ r2_hidden(k4_tarski(A_54,B_55),C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1055,plain,(
    ! [A_187,C_188] :
      ( r2_hidden('#skF_5'(A_187,k1_relat_1(A_187),C_188),k11_relat_1(A_187,C_188))
      | ~ v1_relat_1(A_187)
      | ~ r2_hidden(C_188,k1_relat_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_463,c_48])).

tff(c_1075,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_1055])).

tff(c_1080,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_50,c_1075])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_1080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.45  
% 3.03/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 3.19/1.46  
% 3.19/1.46  %Foreground sorts:
% 3.19/1.46  
% 3.19/1.46  
% 3.19/1.46  %Background operators:
% 3.19/1.46  
% 3.19/1.46  
% 3.19/1.46  %Foreground operators:
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.19/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.46  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.19/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.19/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.19/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.19/1.46  
% 3.19/1.47  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.19/1.47  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.19/1.47  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.19/1.47  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.19/1.47  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.19/1.47  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.19/1.47  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.19/1.47  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.19/1.47  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.19/1.47  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.19/1.47  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.19/1.47  tff(f_74, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.19/1.47  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.47  tff(c_30, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.47  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.47  tff(c_87, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.19/1.47  tff(c_96, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_87])).
% 3.19/1.47  tff(c_99, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_96])).
% 3.19/1.47  tff(c_337, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k3_xboole_0(A_111, B_112))=k4_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.47  tff(c_346, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_99, c_337])).
% 3.19/1.47  tff(c_349, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_346])).
% 3.19/1.47  tff(c_26, plain, (![B_31]: (k4_xboole_0(k1_tarski(B_31), k1_tarski(B_31))!=k1_tarski(B_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.47  tff(c_350, plain, (![B_31]: (k1_tarski(B_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_26])).
% 3.19/1.47  tff(c_317, plain, (![A_106, B_107]: (r1_tarski(k1_tarski(A_106), B_107) | ~r2_hidden(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.47  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.47  tff(c_322, plain, (![A_106]: (k1_tarski(A_106)=k1_xboole_0 | ~r2_hidden(A_106, k1_xboole_0))), inference(resolution, [status(thm)], [c_317, c_6])).
% 3.19/1.47  tff(c_358, plain, (![A_106]: (~r2_hidden(A_106, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_350, c_322])).
% 3.19/1.47  tff(c_58, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.47  tff(c_109, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 3.19/1.47  tff(c_50, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.47  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.47  tff(c_210, plain, (![A_93, B_94, C_95]: (r2_hidden(k4_tarski(A_93, B_94), C_95) | ~r2_hidden(B_94, k11_relat_1(C_95, A_93)) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.19/1.47  tff(c_36, plain, (![C_50, A_35, D_53]: (r2_hidden(C_50, k1_relat_1(A_35)) | ~r2_hidden(k4_tarski(C_50, D_53), A_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.47  tff(c_225, plain, (![A_96, C_97, B_98]: (r2_hidden(A_96, k1_relat_1(C_97)) | ~r2_hidden(B_98, k11_relat_1(C_97, A_96)) | ~v1_relat_1(C_97))), inference(resolution, [status(thm)], [c_210, c_36])).
% 3.19/1.47  tff(c_280, plain, (![A_102, C_103]: (r2_hidden(A_102, k1_relat_1(C_103)) | ~v1_relat_1(C_103) | k11_relat_1(C_103, A_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_225])).
% 3.19/1.47  tff(c_52, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.47  tff(c_167, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_109, c_52])).
% 3.19/1.47  tff(c_291, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_167])).
% 3.19/1.47  tff(c_299, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_291])).
% 3.19/1.47  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_299])).
% 3.19/1.47  tff(c_302, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 3.19/1.47  tff(c_303, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.19/1.47  tff(c_463, plain, (![C_146, A_147]: (r2_hidden(k4_tarski(C_146, '#skF_5'(A_147, k1_relat_1(A_147), C_146)), A_147) | ~r2_hidden(C_146, k1_relat_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.47  tff(c_48, plain, (![B_55, C_56, A_54]: (r2_hidden(B_55, k11_relat_1(C_56, A_54)) | ~r2_hidden(k4_tarski(A_54, B_55), C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.19/1.47  tff(c_1055, plain, (![A_187, C_188]: (r2_hidden('#skF_5'(A_187, k1_relat_1(A_187), C_188), k11_relat_1(A_187, C_188)) | ~v1_relat_1(A_187) | ~r2_hidden(C_188, k1_relat_1(A_187)))), inference(resolution, [status(thm)], [c_463, c_48])).
% 3.19/1.47  tff(c_1075, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_303, c_1055])).
% 3.19/1.47  tff(c_1080, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_302, c_50, c_1075])).
% 3.19/1.47  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_1080])).
% 3.19/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  Inference rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Ref     : 0
% 3.19/1.47  #Sup     : 217
% 3.19/1.47  #Fact    : 0
% 3.19/1.47  #Define  : 0
% 3.19/1.47  #Split   : 3
% 3.19/1.47  #Chain   : 0
% 3.19/1.47  #Close   : 0
% 3.19/1.47  
% 3.19/1.47  Ordering : KBO
% 3.19/1.47  
% 3.19/1.47  Simplification rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Subsume      : 39
% 3.19/1.47  #Demod        : 77
% 3.19/1.47  #Tautology    : 80
% 3.19/1.47  #SimpNegUnit  : 37
% 3.19/1.47  #BackRed      : 6
% 3.19/1.47  
% 3.19/1.47  #Partial instantiations: 0
% 3.19/1.47  #Strategies tried      : 1
% 3.19/1.47  
% 3.19/1.47  Timing (in seconds)
% 3.19/1.47  ----------------------
% 3.19/1.47  Preprocessing        : 0.33
% 3.19/1.47  Parsing              : 0.17
% 3.19/1.47  CNF conversion       : 0.02
% 3.19/1.47  Main loop            : 0.37
% 3.19/1.47  Inferencing          : 0.14
% 3.19/1.47  Reduction            : 0.11
% 3.19/1.47  Demodulation         : 0.07
% 3.19/1.47  BG Simplification    : 0.02
% 3.19/1.47  Subsumption          : 0.07
% 3.19/1.47  Abstraction          : 0.02
% 3.19/1.47  MUC search           : 0.00
% 3.19/1.48  Cooper               : 0.00
% 3.19/1.48  Total                : 0.73
% 3.19/1.48  Index Insertion      : 0.00
% 3.19/1.48  Index Deletion       : 0.00
% 3.19/1.48  Index Matching       : 0.00
% 3.19/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
