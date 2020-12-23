%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   81 (1190 expanded)
%              Number of leaves         :   36 ( 452 expanded)
%              Depth                    :   20
%              Number of atoms          :  101 (2094 expanded)
%              Number of equality atoms :   48 ( 965 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_48,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ! [A_45] : v1_relat_1(k6_relat_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_45] : v1_funct_1(k6_relat_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_42] : k1_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_42] : k2_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [A_71] :
      ( k10_relat_1(A_71,k2_relat_1(A_71)) = k1_relat_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [A_42] :
      ( k10_relat_1(k6_relat_1(A_42),A_42) = k1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_122,plain,(
    ! [A_42] : k10_relat_1(k6_relat_1(A_42),A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_118])).

tff(c_325,plain,(
    ! [A_115,C_116,B_117] :
      ( k3_xboole_0(A_115,k10_relat_1(C_116,B_117)) = k10_relat_1(k7_relat_1(C_116,A_115),B_117)
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_411,plain,(
    ! [A_42,A_115] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_42),A_115),A_42) = k3_xboole_0(A_115,A_42)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_325])).

tff(c_418,plain,(
    ! [A_42,A_115] : k10_relat_1(k7_relat_1(k6_relat_1(A_42),A_115),A_42) = k3_xboole_0(A_115,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_411])).

tff(c_34,plain,(
    ! [A_43,B_44] :
      ( k5_relat_1(k6_relat_1(A_43),B_44) = k7_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_623,plain,(
    ! [B_144,C_145,A_146] :
      ( k10_relat_1(k5_relat_1(B_144,C_145),A_146) = k10_relat_1(B_144,k10_relat_1(C_145,A_146))
      | ~ v1_relat_1(C_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_639,plain,(
    ! [A_43,B_44,A_146] :
      ( k10_relat_1(k6_relat_1(A_43),k10_relat_1(B_44,A_146)) = k10_relat_1(k7_relat_1(B_44,A_43),A_146)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_623])).

tff(c_840,plain,(
    ! [A_162,B_163,A_164] :
      ( k10_relat_1(k6_relat_1(A_162),k10_relat_1(B_163,A_164)) = k10_relat_1(k7_relat_1(B_163,A_162),A_164)
      | ~ v1_relat_1(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_639])).

tff(c_868,plain,(
    ! [A_42,A_162] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_42),A_162),A_42) = k10_relat_1(k6_relat_1(A_162),A_42)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_840])).

tff(c_887,plain,(
    ! [A_165,A_166] : k10_relat_1(k6_relat_1(A_165),A_166) = k3_xboole_0(A_165,A_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_418,c_868])).

tff(c_897,plain,(
    ! [A_166] : k3_xboole_0(A_166,A_166) = A_166 ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_122])).

tff(c_885,plain,(
    ! [A_162,A_42] : k10_relat_1(k6_relat_1(A_162),A_42) = k3_xboole_0(A_162,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_418,c_868])).

tff(c_1083,plain,(
    ! [B_168,A_169] :
      ( k9_relat_1(B_168,k10_relat_1(B_168,A_169)) = A_169
      | ~ r1_tarski(A_169,k2_relat_1(B_168))
      | ~ v1_funct_1(B_168)
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1109,plain,(
    ! [A_42,A_169] :
      ( k9_relat_1(k6_relat_1(A_42),k10_relat_1(k6_relat_1(A_42),A_169)) = A_169
      | ~ r1_tarski(A_169,A_42)
      | ~ v1_funct_1(k6_relat_1(A_42))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1083])).

tff(c_1126,plain,(
    ! [A_170,A_171] :
      ( k9_relat_1(k6_relat_1(A_170),k3_xboole_0(A_170,A_171)) = A_171
      | ~ r1_tarski(A_171,A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_885,c_1109])).

tff(c_1135,plain,(
    ! [A_166] :
      ( k9_relat_1(k6_relat_1(A_166),A_166) = A_166
      | ~ r1_tarski(A_166,A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_1126])).

tff(c_1142,plain,(
    ! [A_166] : k9_relat_1(k6_relat_1(A_166),A_166) = A_166 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1135])).

tff(c_1379,plain,(
    ! [A_183,B_184] :
      ( k3_xboole_0(A_183,k9_relat_1(B_184,k1_relat_1(B_184))) = k9_relat_1(B_184,k10_relat_1(B_184,A_183))
      | ~ v1_funct_1(B_184)
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1529,plain,(
    ! [A_42,A_183] :
      ( k9_relat_1(k6_relat_1(A_42),k10_relat_1(k6_relat_1(A_42),A_183)) = k3_xboole_0(A_183,k9_relat_1(k6_relat_1(A_42),A_42))
      | ~ v1_funct_1(k6_relat_1(A_42))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1379])).

tff(c_1533,plain,(
    ! [A_42,A_183] : k9_relat_1(k6_relat_1(A_42),k3_xboole_0(A_42,A_183)) = k3_xboole_0(A_183,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_1142,c_885,c_1529])).

tff(c_1122,plain,(
    ! [A_42,A_169] :
      ( k9_relat_1(k6_relat_1(A_42),k3_xboole_0(A_42,A_169)) = A_169
      | ~ r1_tarski(A_169,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_885,c_1109])).

tff(c_1554,plain,(
    ! [A_187,A_188] :
      ( k3_xboole_0(A_187,A_188) = A_187
      | ~ r1_tarski(A_187,A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_1122])).

tff(c_1621,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1554])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1620,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_1554])).

tff(c_1624,plain,(
    ! [A_189,B_190] : k3_xboole_0(k3_xboole_0(A_189,B_190),A_189) = k3_xboole_0(A_189,B_190) ),
    inference(resolution,[status(thm)],[c_8,c_1554])).

tff(c_1633,plain,(
    ! [A_189,B_190] : k9_relat_1(k6_relat_1(k3_xboole_0(A_189,B_190)),k3_xboole_0(A_189,B_190)) = k3_xboole_0(A_189,k3_xboole_0(A_189,B_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_1533])).

tff(c_1838,plain,(
    ! [A_191,B_192] : k3_xboole_0(A_191,k3_xboole_0(A_191,B_192)) = k3_xboole_0(A_191,B_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1633])).

tff(c_1850,plain,(
    ! [A_191,B_192] : k9_relat_1(k6_relat_1(A_191),k3_xboole_0(A_191,B_192)) = k3_xboole_0(k3_xboole_0(A_191,B_192),A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_1838,c_1533])).

tff(c_2029,plain,(
    ! [B_193,A_194] : k3_xboole_0(B_193,A_194) = k3_xboole_0(A_194,B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1533,c_1850])).

tff(c_2358,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_2029])).

tff(c_40,plain,(
    ! [A_46,C_48,B_47] :
      ( k3_xboole_0(A_46,k10_relat_1(C_48,B_47)) = k10_relat_1(k7_relat_1(C_48,A_46),B_47)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2901,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2358,c_40])).

tff(c_2937,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2901])).

tff(c_2939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.77  
% 4.01/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.77  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.01/1.77  
% 4.01/1.77  %Foreground sorts:
% 4.01/1.77  
% 4.01/1.77  
% 4.01/1.77  %Background operators:
% 4.01/1.77  
% 4.01/1.77  
% 4.01/1.77  %Foreground operators:
% 4.01/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.77  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.01/1.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.01/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.01/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.01/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.01/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.77  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.01/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.77  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.01/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.01/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.01/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.01/1.77  
% 4.44/1.79  tff(f_114, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 4.44/1.79  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.44/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.44/1.79  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.44/1.79  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.44/1.79  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.44/1.79  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.44/1.79  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 4.44/1.79  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 4.44/1.79  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 4.44/1.79  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.44/1.79  tff(c_48, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.44/1.79  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.44/1.79  tff(c_50, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.44/1.79  tff(c_36, plain, (![A_45]: (v1_relat_1(k6_relat_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.44/1.79  tff(c_38, plain, (![A_45]: (v1_funct_1(k6_relat_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.44/1.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.44/1.79  tff(c_30, plain, (![A_42]: (k1_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.44/1.79  tff(c_32, plain, (![A_42]: (k2_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.44/1.79  tff(c_109, plain, (![A_71]: (k10_relat_1(A_71, k2_relat_1(A_71))=k1_relat_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.44/1.79  tff(c_118, plain, (![A_42]: (k10_relat_1(k6_relat_1(A_42), A_42)=k1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_109])).
% 4.44/1.79  tff(c_122, plain, (![A_42]: (k10_relat_1(k6_relat_1(A_42), A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_118])).
% 4.44/1.79  tff(c_325, plain, (![A_115, C_116, B_117]: (k3_xboole_0(A_115, k10_relat_1(C_116, B_117))=k10_relat_1(k7_relat_1(C_116, A_115), B_117) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.79  tff(c_411, plain, (![A_42, A_115]: (k10_relat_1(k7_relat_1(k6_relat_1(A_42), A_115), A_42)=k3_xboole_0(A_115, A_42) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_325])).
% 4.44/1.79  tff(c_418, plain, (![A_42, A_115]: (k10_relat_1(k7_relat_1(k6_relat_1(A_42), A_115), A_42)=k3_xboole_0(A_115, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_411])).
% 4.44/1.79  tff(c_34, plain, (![A_43, B_44]: (k5_relat_1(k6_relat_1(A_43), B_44)=k7_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.44/1.79  tff(c_623, plain, (![B_144, C_145, A_146]: (k10_relat_1(k5_relat_1(B_144, C_145), A_146)=k10_relat_1(B_144, k10_relat_1(C_145, A_146)) | ~v1_relat_1(C_145) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.79  tff(c_639, plain, (![A_43, B_44, A_146]: (k10_relat_1(k6_relat_1(A_43), k10_relat_1(B_44, A_146))=k10_relat_1(k7_relat_1(B_44, A_43), A_146) | ~v1_relat_1(B_44) | ~v1_relat_1(k6_relat_1(A_43)) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_34, c_623])).
% 4.44/1.79  tff(c_840, plain, (![A_162, B_163, A_164]: (k10_relat_1(k6_relat_1(A_162), k10_relat_1(B_163, A_164))=k10_relat_1(k7_relat_1(B_163, A_162), A_164) | ~v1_relat_1(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_639])).
% 4.44/1.79  tff(c_868, plain, (![A_42, A_162]: (k10_relat_1(k7_relat_1(k6_relat_1(A_42), A_162), A_42)=k10_relat_1(k6_relat_1(A_162), A_42) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_840])).
% 4.44/1.79  tff(c_887, plain, (![A_165, A_166]: (k10_relat_1(k6_relat_1(A_165), A_166)=k3_xboole_0(A_165, A_166))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_418, c_868])).
% 4.44/1.79  tff(c_897, plain, (![A_166]: (k3_xboole_0(A_166, A_166)=A_166)), inference(superposition, [status(thm), theory('equality')], [c_887, c_122])).
% 4.44/1.79  tff(c_885, plain, (![A_162, A_42]: (k10_relat_1(k6_relat_1(A_162), A_42)=k3_xboole_0(A_162, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_418, c_868])).
% 4.44/1.79  tff(c_1083, plain, (![B_168, A_169]: (k9_relat_1(B_168, k10_relat_1(B_168, A_169))=A_169 | ~r1_tarski(A_169, k2_relat_1(B_168)) | ~v1_funct_1(B_168) | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.44/1.79  tff(c_1109, plain, (![A_42, A_169]: (k9_relat_1(k6_relat_1(A_42), k10_relat_1(k6_relat_1(A_42), A_169))=A_169 | ~r1_tarski(A_169, A_42) | ~v1_funct_1(k6_relat_1(A_42)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1083])).
% 4.44/1.79  tff(c_1126, plain, (![A_170, A_171]: (k9_relat_1(k6_relat_1(A_170), k3_xboole_0(A_170, A_171))=A_171 | ~r1_tarski(A_171, A_170))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_885, c_1109])).
% 4.44/1.79  tff(c_1135, plain, (![A_166]: (k9_relat_1(k6_relat_1(A_166), A_166)=A_166 | ~r1_tarski(A_166, A_166))), inference(superposition, [status(thm), theory('equality')], [c_897, c_1126])).
% 4.44/1.79  tff(c_1142, plain, (![A_166]: (k9_relat_1(k6_relat_1(A_166), A_166)=A_166)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1135])).
% 4.44/1.79  tff(c_1379, plain, (![A_183, B_184]: (k3_xboole_0(A_183, k9_relat_1(B_184, k1_relat_1(B_184)))=k9_relat_1(B_184, k10_relat_1(B_184, A_183)) | ~v1_funct_1(B_184) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.44/1.79  tff(c_1529, plain, (![A_42, A_183]: (k9_relat_1(k6_relat_1(A_42), k10_relat_1(k6_relat_1(A_42), A_183))=k3_xboole_0(A_183, k9_relat_1(k6_relat_1(A_42), A_42)) | ~v1_funct_1(k6_relat_1(A_42)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1379])).
% 4.44/1.79  tff(c_1533, plain, (![A_42, A_183]: (k9_relat_1(k6_relat_1(A_42), k3_xboole_0(A_42, A_183))=k3_xboole_0(A_183, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_1142, c_885, c_1529])).
% 4.44/1.79  tff(c_1122, plain, (![A_42, A_169]: (k9_relat_1(k6_relat_1(A_42), k3_xboole_0(A_42, A_169))=A_169 | ~r1_tarski(A_169, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_885, c_1109])).
% 4.44/1.79  tff(c_1554, plain, (![A_187, A_188]: (k3_xboole_0(A_187, A_188)=A_187 | ~r1_tarski(A_187, A_188))), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_1122])).
% 4.44/1.79  tff(c_1621, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1554])).
% 4.44/1.79  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.44/1.79  tff(c_1620, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_1554])).
% 4.44/1.79  tff(c_1624, plain, (![A_189, B_190]: (k3_xboole_0(k3_xboole_0(A_189, B_190), A_189)=k3_xboole_0(A_189, B_190))), inference(resolution, [status(thm)], [c_8, c_1554])).
% 4.44/1.79  tff(c_1633, plain, (![A_189, B_190]: (k9_relat_1(k6_relat_1(k3_xboole_0(A_189, B_190)), k3_xboole_0(A_189, B_190))=k3_xboole_0(A_189, k3_xboole_0(A_189, B_190)))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_1533])).
% 4.44/1.79  tff(c_1838, plain, (![A_191, B_192]: (k3_xboole_0(A_191, k3_xboole_0(A_191, B_192))=k3_xboole_0(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1633])).
% 4.44/1.79  tff(c_1850, plain, (![A_191, B_192]: (k9_relat_1(k6_relat_1(A_191), k3_xboole_0(A_191, B_192))=k3_xboole_0(k3_xboole_0(A_191, B_192), A_191))), inference(superposition, [status(thm), theory('equality')], [c_1838, c_1533])).
% 4.44/1.79  tff(c_2029, plain, (![B_193, A_194]: (k3_xboole_0(B_193, A_194)=k3_xboole_0(A_194, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1533, c_1850])).
% 4.44/1.79  tff(c_2358, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1621, c_2029])).
% 4.44/1.79  tff(c_40, plain, (![A_46, C_48, B_47]: (k3_xboole_0(A_46, k10_relat_1(C_48, B_47))=k10_relat_1(k7_relat_1(C_48, A_46), B_47) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.44/1.79  tff(c_2901, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2358, c_40])).
% 4.44/1.79  tff(c_2937, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2901])).
% 4.44/1.79  tff(c_2939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_2937])).
% 4.44/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.79  
% 4.44/1.79  Inference rules
% 4.44/1.79  ----------------------
% 4.44/1.79  #Ref     : 0
% 4.44/1.79  #Sup     : 688
% 4.44/1.79  #Fact    : 0
% 4.44/1.79  #Define  : 0
% 4.44/1.79  #Split   : 1
% 4.44/1.79  #Chain   : 0
% 4.44/1.79  #Close   : 0
% 4.44/1.79  
% 4.44/1.79  Ordering : KBO
% 4.44/1.79  
% 4.44/1.79  Simplification rules
% 4.44/1.79  ----------------------
% 4.44/1.79  #Subsume      : 49
% 4.44/1.79  #Demod        : 286
% 4.44/1.79  #Tautology    : 256
% 4.44/1.79  #SimpNegUnit  : 1
% 4.44/1.79  #BackRed      : 2
% 4.44/1.79  
% 4.44/1.79  #Partial instantiations: 0
% 4.44/1.79  #Strategies tried      : 1
% 4.44/1.79  
% 4.44/1.79  Timing (in seconds)
% 4.44/1.79  ----------------------
% 4.44/1.79  Preprocessing        : 0.35
% 4.44/1.79  Parsing              : 0.19
% 4.44/1.79  CNF conversion       : 0.02
% 4.44/1.79  Main loop            : 0.63
% 4.44/1.79  Inferencing          : 0.21
% 4.44/1.79  Reduction            : 0.23
% 4.44/1.79  Demodulation         : 0.18
% 4.44/1.79  BG Simplification    : 0.03
% 4.44/1.79  Subsumption          : 0.12
% 4.44/1.79  Abstraction          : 0.04
% 4.44/1.79  MUC search           : 0.00
% 4.44/1.79  Cooper               : 0.00
% 4.44/1.79  Total                : 1.01
% 4.44/1.79  Index Insertion      : 0.00
% 4.44/1.79  Index Deletion       : 0.00
% 4.44/1.79  Index Matching       : 0.00
% 4.44/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
