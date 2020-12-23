%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 108 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_32,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [B_22,A_21] : k5_relat_1(k6_relat_1(B_22),k6_relat_1(A_21)) = k6_relat_1(k3_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_269,plain,(
    ! [A_53,B_54] :
      ( k10_relat_1(A_53,k1_relat_1(B_54)) = k1_relat_1(k5_relat_1(A_53,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_315,plain,(
    ! [A_53,A_16] :
      ( k1_relat_1(k5_relat_1(A_53,k6_relat_1(A_16))) = k10_relat_1(A_53,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_269])).

tff(c_444,plain,(
    ! [A_69,A_70] :
      ( k1_relat_1(k5_relat_1(A_69,k6_relat_1(A_70))) = k10_relat_1(A_69,A_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_315])).

tff(c_463,plain,(
    ! [A_21,B_22] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_21,B_22))) = k10_relat_1(k6_relat_1(B_22),A_21)
      | ~ v1_relat_1(k6_relat_1(B_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_444])).

tff(c_469,plain,(
    ! [B_22,A_21] : k10_relat_1(k6_relat_1(B_22),A_21) = k3_xboole_0(A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_463])).

tff(c_79,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k10_relat_1(B_34,A_35),k1_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_16,A_35] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_16),A_35),A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_79])).

tff(c_84,plain,(
    ! [A_16,A_35] : r1_tarski(k10_relat_1(k6_relat_1(A_16),A_35),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_82])).

tff(c_22,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,(
    ! [A_40] :
      ( k10_relat_1(A_40,k2_relat_1(A_40)) = k1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_16] :
      ( k10_relat_1(k6_relat_1(A_16),A_16) = k1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_125,plain,(
    ! [A_16] : k10_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_118])).

tff(c_154,plain,(
    ! [C_44,A_45,B_46] :
      ( r1_tarski(k10_relat_1(C_44,A_45),k10_relat_1(C_44,B_46))
      | ~ r1_tarski(A_45,B_46)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    ! [A_16,B_46] :
      ( r1_tarski(A_16,k10_relat_1(k6_relat_1(A_16),B_46))
      | ~ r1_tarski(A_16,B_46)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_154])).

tff(c_174,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k10_relat_1(k6_relat_1(A_47),B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [A_47,B_48] :
      ( k10_relat_1(k6_relat_1(A_47),B_48) = A_47
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_47),B_48),A_47)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_186,plain,(
    ! [A_47,B_48] :
      ( k10_relat_1(k6_relat_1(A_47),B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_176])).

tff(c_591,plain,(
    ! [B_76,A_77] :
      ( k3_xboole_0(B_76,A_77) = A_77
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_186])).

tff(c_622,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_591])).

tff(c_28,plain,(
    ! [A_18,C_20,B_19] :
      ( k3_xboole_0(A_18,k10_relat_1(C_20,B_19)) = k10_relat_1(k7_relat_1(C_20,A_18),B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_659,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_28])).

tff(c_671,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_659])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.33  
% 2.60/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.33  
% 2.60/1.33  %Foreground sorts:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Background operators:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Foreground operators:
% 2.60/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.60/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.60/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.60/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.60/1.33  
% 2.60/1.34  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.60/1.34  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.60/1.34  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.60/1.34  tff(f_70, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.60/1.34  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.60/1.34  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.60/1.34  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.60/1.34  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.60/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.34  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.60/1.34  tff(c_32, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.34  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.34  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.34  tff(c_24, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.34  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.60/1.34  tff(c_30, plain, (![B_22, A_21]: (k5_relat_1(k6_relat_1(B_22), k6_relat_1(A_21))=k6_relat_1(k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.34  tff(c_269, plain, (![A_53, B_54]: (k10_relat_1(A_53, k1_relat_1(B_54))=k1_relat_1(k5_relat_1(A_53, B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.34  tff(c_315, plain, (![A_53, A_16]: (k1_relat_1(k5_relat_1(A_53, k6_relat_1(A_16)))=k10_relat_1(A_53, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_20, c_269])).
% 2.60/1.34  tff(c_444, plain, (![A_69, A_70]: (k1_relat_1(k5_relat_1(A_69, k6_relat_1(A_70)))=k10_relat_1(A_69, A_70) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_315])).
% 2.60/1.34  tff(c_463, plain, (![A_21, B_22]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_21, B_22)))=k10_relat_1(k6_relat_1(B_22), A_21) | ~v1_relat_1(k6_relat_1(B_22)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_444])).
% 2.60/1.34  tff(c_469, plain, (![B_22, A_21]: (k10_relat_1(k6_relat_1(B_22), A_21)=k3_xboole_0(A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_463])).
% 2.60/1.34  tff(c_79, plain, (![B_34, A_35]: (r1_tarski(k10_relat_1(B_34, A_35), k1_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.34  tff(c_82, plain, (![A_16, A_35]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_35), A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_79])).
% 2.60/1.34  tff(c_84, plain, (![A_16, A_35]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_35), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_82])).
% 2.60/1.34  tff(c_22, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.60/1.34  tff(c_102, plain, (![A_40]: (k10_relat_1(A_40, k2_relat_1(A_40))=k1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.34  tff(c_118, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=k1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_102])).
% 2.60/1.34  tff(c_125, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_118])).
% 2.60/1.34  tff(c_154, plain, (![C_44, A_45, B_46]: (r1_tarski(k10_relat_1(C_44, A_45), k10_relat_1(C_44, B_46)) | ~r1_tarski(A_45, B_46) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.34  tff(c_159, plain, (![A_16, B_46]: (r1_tarski(A_16, k10_relat_1(k6_relat_1(A_16), B_46)) | ~r1_tarski(A_16, B_46) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_154])).
% 2.60/1.34  tff(c_174, plain, (![A_47, B_48]: (r1_tarski(A_47, k10_relat_1(k6_relat_1(A_47), B_48)) | ~r1_tarski(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_159])).
% 2.60/1.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.34  tff(c_176, plain, (![A_47, B_48]: (k10_relat_1(k6_relat_1(A_47), B_48)=A_47 | ~r1_tarski(k10_relat_1(k6_relat_1(A_47), B_48), A_47) | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_174, c_2])).
% 2.60/1.34  tff(c_186, plain, (![A_47, B_48]: (k10_relat_1(k6_relat_1(A_47), B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_176])).
% 2.60/1.34  tff(c_591, plain, (![B_76, A_77]: (k3_xboole_0(B_76, A_77)=A_77 | ~r1_tarski(A_77, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_186])).
% 2.60/1.34  tff(c_622, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_591])).
% 2.60/1.34  tff(c_28, plain, (![A_18, C_20, B_19]: (k3_xboole_0(A_18, k10_relat_1(C_20, B_19))=k10_relat_1(k7_relat_1(C_20, A_18), B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.60/1.34  tff(c_659, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_622, c_28])).
% 2.60/1.34  tff(c_671, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_659])).
% 2.60/1.34  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_671])).
% 2.60/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  Inference rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Ref     : 0
% 2.60/1.34  #Sup     : 138
% 2.60/1.34  #Fact    : 0
% 2.60/1.34  #Define  : 0
% 2.60/1.34  #Split   : 1
% 2.60/1.34  #Chain   : 0
% 2.60/1.34  #Close   : 0
% 2.60/1.34  
% 2.60/1.34  Ordering : KBO
% 2.60/1.34  
% 2.60/1.34  Simplification rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Subsume      : 8
% 2.60/1.34  #Demod        : 122
% 2.60/1.34  #Tautology    : 64
% 2.60/1.34  #SimpNegUnit  : 1
% 2.60/1.34  #BackRed      : 4
% 2.60/1.34  
% 2.60/1.34  #Partial instantiations: 0
% 2.60/1.34  #Strategies tried      : 1
% 2.60/1.34  
% 2.60/1.35  Timing (in seconds)
% 2.60/1.35  ----------------------
% 2.60/1.35  Preprocessing        : 0.30
% 2.60/1.35  Parsing              : 0.16
% 2.60/1.35  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.28
% 2.60/1.35  Inferencing          : 0.10
% 2.60/1.35  Reduction            : 0.10
% 2.60/1.35  Demodulation         : 0.07
% 2.60/1.35  BG Simplification    : 0.02
% 2.60/1.35  Subsumption          : 0.05
% 2.60/1.35  Abstraction          : 0.02
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.62
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
