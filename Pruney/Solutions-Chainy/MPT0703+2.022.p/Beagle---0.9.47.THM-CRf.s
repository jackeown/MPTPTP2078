%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 101 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 173 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(c_77,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_85,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_30])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_86,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_455,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_470,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_455])).

tff(c_475,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_470])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_145,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_145])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_229,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(k2_xboole_0(A_49,B_51),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_249,plain,(
    ! [A_52,B_53] : r1_tarski(A_52,k2_xboole_0(A_52,B_53)) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_375,plain,(
    ! [A_60,B_61,B_62] : r1_tarski(A_60,k2_xboole_0(k2_xboole_0(A_60,B_61),B_62)) ),
    inference(resolution,[status(thm)],[c_249,c_14])).

tff(c_417,plain,(
    ! [A_63,B_64,B_65] : r1_tarski(k3_xboole_0(A_63,B_64),k2_xboole_0(A_63,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_375])).

tff(c_513,plain,(
    ! [B_69] : r1_tarski(k3_xboole_0('#skF_1',B_69),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_417])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_538,plain,(
    ! [B_69] : k4_xboole_0(k3_xboole_0('#skF_1',B_69),k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_513,c_10])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_654,plain,(
    ! [B_76,A_77] :
      ( k9_relat_1(B_76,k10_relat_1(B_76,A_77)) = A_77
      | ~ r1_tarski(A_77,k2_relat_1(B_76))
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_667,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_654])).

tff(c_679,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_667])).

tff(c_1004,plain,(
    ! [C_92,A_93,B_94] :
      ( k3_xboole_0(k10_relat_1(C_92,A_93),k10_relat_1(C_92,B_94)) = k10_relat_1(C_92,k3_xboole_0(A_93,B_94))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_103,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_1013,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_103])).

tff(c_1051,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1013])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3104,plain,(
    ! [B_166,A_167] :
      ( k9_relat_1(B_166,k10_relat_1(B_166,A_167)) = A_167
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166)
      | k4_xboole_0(A_167,k2_relat_1(B_166)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_654])).

tff(c_3123,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_3104])).

tff(c_3139,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_38,c_36,c_679,c_3123])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3208,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3139,c_12])).

tff(c_3243,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_3208])).

tff(c_3245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_3243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:53:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.64  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.91/1.64  
% 3.91/1.64  %Foreground sorts:
% 3.91/1.64  
% 3.91/1.64  
% 3.91/1.64  %Background operators:
% 3.91/1.64  
% 3.91/1.64  
% 3.91/1.64  %Foreground operators:
% 3.91/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.91/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.91/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.91/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.91/1.64  
% 3.91/1.66  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.91/1.66  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.91/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.66  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.91/1.66  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.91/1.66  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.91/1.66  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.91/1.66  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.91/1.66  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.91/1.66  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 3.91/1.66  tff(c_77, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.66  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.66  tff(c_85, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_30])).
% 3.91/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.66  tff(c_42, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.66  tff(c_54, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_42])).
% 3.91/1.66  tff(c_86, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.66  tff(c_106, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_86])).
% 3.91/1.66  tff(c_455, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.91/1.66  tff(c_470, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_106, c_455])).
% 3.91/1.66  tff(c_475, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_470])).
% 3.91/1.66  tff(c_32, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.66  tff(c_145, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.91/1.66  tff(c_164, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_145])).
% 3.91/1.66  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.66  tff(c_163, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), A_12)=A_12)), inference(resolution, [status(thm)], [c_18, c_145])).
% 3.91/1.66  tff(c_229, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(k2_xboole_0(A_49, B_51), C_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.66  tff(c_249, plain, (![A_52, B_53]: (r1_tarski(A_52, k2_xboole_0(A_52, B_53)))), inference(resolution, [status(thm)], [c_6, c_229])).
% 3.91/1.66  tff(c_14, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.66  tff(c_375, plain, (![A_60, B_61, B_62]: (r1_tarski(A_60, k2_xboole_0(k2_xboole_0(A_60, B_61), B_62)))), inference(resolution, [status(thm)], [c_249, c_14])).
% 3.91/1.66  tff(c_417, plain, (![A_63, B_64, B_65]: (r1_tarski(k3_xboole_0(A_63, B_64), k2_xboole_0(A_63, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_375])).
% 3.91/1.66  tff(c_513, plain, (![B_69]: (r1_tarski(k3_xboole_0('#skF_1', B_69), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_164, c_417])).
% 3.91/1.66  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.66  tff(c_538, plain, (![B_69]: (k4_xboole_0(k3_xboole_0('#skF_1', B_69), k2_relat_1('#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_513, c_10])).
% 3.91/1.66  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.66  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.66  tff(c_654, plain, (![B_76, A_77]: (k9_relat_1(B_76, k10_relat_1(B_76, A_77))=A_77 | ~r1_tarski(A_77, k2_relat_1(B_76)) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.91/1.66  tff(c_667, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_654])).
% 3.91/1.66  tff(c_679, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_667])).
% 3.91/1.66  tff(c_1004, plain, (![C_92, A_93, B_94]: (k3_xboole_0(k10_relat_1(C_92, A_93), k10_relat_1(C_92, B_94))=k10_relat_1(C_92, k3_xboole_0(A_93, B_94)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.91/1.66  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.66  tff(c_103, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_86])).
% 3.91/1.66  tff(c_1013, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1004, c_103])).
% 3.91/1.66  tff(c_1051, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1013])).
% 3.91/1.66  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.66  tff(c_3104, plain, (![B_166, A_167]: (k9_relat_1(B_166, k10_relat_1(B_166, A_167))=A_167 | ~v1_funct_1(B_166) | ~v1_relat_1(B_166) | k4_xboole_0(A_167, k2_relat_1(B_166))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_654])).
% 3.91/1.66  tff(c_3123, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1051, c_3104])).
% 3.91/1.66  tff(c_3139, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_38, c_36, c_679, c_3123])).
% 3.91/1.66  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.91/1.66  tff(c_3208, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3139, c_12])).
% 3.91/1.66  tff(c_3243, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_475, c_3208])).
% 3.91/1.66  tff(c_3245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_3243])).
% 3.91/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.66  
% 3.91/1.66  Inference rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Ref     : 0
% 3.91/1.66  #Sup     : 786
% 3.91/1.66  #Fact    : 0
% 3.91/1.66  #Define  : 0
% 3.91/1.66  #Split   : 2
% 3.91/1.66  #Chain   : 0
% 3.91/1.66  #Close   : 0
% 3.91/1.66  
% 3.91/1.66  Ordering : KBO
% 3.91/1.66  
% 3.91/1.66  Simplification rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Subsume      : 43
% 3.91/1.66  #Demod        : 477
% 3.91/1.66  #Tautology    : 502
% 3.91/1.66  #SimpNegUnit  : 1
% 3.91/1.66  #BackRed      : 0
% 3.91/1.66  
% 3.91/1.66  #Partial instantiations: 0
% 3.91/1.66  #Strategies tried      : 1
% 3.91/1.66  
% 3.91/1.66  Timing (in seconds)
% 3.91/1.66  ----------------------
% 3.91/1.66  Preprocessing        : 0.30
% 3.91/1.66  Parsing              : 0.16
% 3.91/1.66  CNF conversion       : 0.02
% 3.91/1.66  Main loop            : 0.63
% 3.91/1.66  Inferencing          : 0.21
% 3.91/1.66  Reduction            : 0.24
% 3.91/1.66  Demodulation         : 0.18
% 3.91/1.66  BG Simplification    : 0.02
% 3.91/1.66  Subsumption          : 0.11
% 3.91/1.66  Abstraction          : 0.04
% 3.91/1.66  MUC search           : 0.00
% 3.91/1.66  Cooper               : 0.00
% 3.91/1.66  Total                : 0.96
% 3.91/1.66  Index Insertion      : 0.00
% 3.91/1.66  Index Deletion       : 0.00
% 3.91/1.66  Index Matching       : 0.00
% 3.91/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
