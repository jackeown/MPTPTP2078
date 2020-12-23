%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:07 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 (  79 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_316,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_336,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_58,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_316])).

tff(c_621,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(k2_xboole_0(A_95,C_96),B_97)
      | ~ r1_tarski(C_96,B_97)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_267,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_280,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_267])).

tff(c_645,plain,(
    ! [B_97,C_96] :
      ( k2_xboole_0(B_97,C_96) = B_97
      | ~ r1_tarski(C_96,B_97)
      | ~ r1_tarski(B_97,B_97) ) ),
    inference(resolution,[status(thm)],[c_621,c_280])).

tff(c_681,plain,(
    ! [B_98,C_99] :
      ( k2_xboole_0(B_98,C_99) = B_98
      | ~ r1_tarski(C_99,B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_645])).

tff(c_1545,plain,(
    ! [A_117] :
      ( k2_xboole_0(k2_relat_1('#skF_2'),A_117) = k2_relat_1('#skF_2')
      | ~ r1_tarski(A_117,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_336,c_681])).

tff(c_81,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,k2_xboole_0(A_37,B_36)) = B_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_2544,plain,(
    ! [A_132] :
      ( k3_xboole_0(A_132,k2_relat_1('#skF_2')) = A_132
      | ~ r1_tarski(A_132,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_99])).

tff(c_22,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_173,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_211,plain,(
    ! [B_48,A_49] : k1_setfam_1(k2_tarski(B_48,A_49)) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_173])).

tff(c_26,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_217,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_26])).

tff(c_3826,plain,(
    ! [A_155] :
      ( k3_xboole_0(k2_relat_1('#skF_2'),A_155) = A_155
      | ~ r1_tarski(A_155,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2544,c_217])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( k3_xboole_0(k2_relat_1(B_26),A_25) = k2_relat_1(k8_relat_1(A_25,B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3840,plain,(
    ! [A_155] :
      ( k2_relat_1(k8_relat_1(A_155,'#skF_2')) = A_155
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_155,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3826,c_28])).

tff(c_4636,plain,(
    ! [A_167] :
      ( k2_relat_1(k8_relat_1(A_167,'#skF_2')) = A_167
      | ~ r1_tarski(A_167,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3840])).

tff(c_30,plain,(
    k2_relat_1(k8_relat_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4662,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4636,c_30])).

tff(c_4685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.87  
% 4.75/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.88  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.75/1.88  
% 4.75/1.88  %Foreground sorts:
% 4.75/1.88  
% 4.75/1.88  
% 4.75/1.88  %Background operators:
% 4.75/1.88  
% 4.75/1.88  
% 4.75/1.88  %Foreground operators:
% 4.75/1.88  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.75/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.75/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.75/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.75/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.75/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.75/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.75/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.75/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.75/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.75/1.88  
% 4.75/1.89  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.75/1.89  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 4.75/1.89  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.75/1.89  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.75/1.89  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.75/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.75/1.89  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.75/1.89  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.75/1.89  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.75/1.89  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 4.75/1.89  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.89  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.75/1.89  tff(c_32, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.75/1.89  tff(c_316, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.75/1.89  tff(c_336, plain, (![A_58]: (r1_tarski(A_58, k2_relat_1('#skF_2')) | ~r1_tarski(A_58, '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_316])).
% 4.75/1.89  tff(c_621, plain, (![A_95, C_96, B_97]: (r1_tarski(k2_xboole_0(A_95, C_96), B_97) | ~r1_tarski(C_96, B_97) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.75/1.89  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.75/1.89  tff(c_267, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.89  tff(c_280, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(k2_xboole_0(A_14, B_15), A_14))), inference(resolution, [status(thm)], [c_18, c_267])).
% 4.75/1.89  tff(c_645, plain, (![B_97, C_96]: (k2_xboole_0(B_97, C_96)=B_97 | ~r1_tarski(C_96, B_97) | ~r1_tarski(B_97, B_97))), inference(resolution, [status(thm)], [c_621, c_280])).
% 4.75/1.89  tff(c_681, plain, (![B_98, C_99]: (k2_xboole_0(B_98, C_99)=B_98 | ~r1_tarski(C_99, B_98))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_645])).
% 4.75/1.89  tff(c_1545, plain, (![A_117]: (k2_xboole_0(k2_relat_1('#skF_2'), A_117)=k2_relat_1('#skF_2') | ~r1_tarski(A_117, '#skF_1'))), inference(resolution, [status(thm)], [c_336, c_681])).
% 4.75/1.89  tff(c_81, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.75/1.89  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.75/1.89  tff(c_99, plain, (![B_36, A_37]: (k3_xboole_0(B_36, k2_xboole_0(A_37, B_36))=B_36)), inference(superposition, [status(thm), theory('equality')], [c_81, c_12])).
% 4.75/1.89  tff(c_2544, plain, (![A_132]: (k3_xboole_0(A_132, k2_relat_1('#skF_2'))=A_132 | ~r1_tarski(A_132, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_99])).
% 4.75/1.89  tff(c_22, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.75/1.89  tff(c_173, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.75/1.89  tff(c_211, plain, (![B_48, A_49]: (k1_setfam_1(k2_tarski(B_48, A_49))=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_22, c_173])).
% 4.75/1.89  tff(c_26, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.75/1.89  tff(c_217, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_211, c_26])).
% 4.75/1.89  tff(c_3826, plain, (![A_155]: (k3_xboole_0(k2_relat_1('#skF_2'), A_155)=A_155 | ~r1_tarski(A_155, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2544, c_217])).
% 4.75/1.89  tff(c_28, plain, (![B_26, A_25]: (k3_xboole_0(k2_relat_1(B_26), A_25)=k2_relat_1(k8_relat_1(A_25, B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.75/1.89  tff(c_3840, plain, (![A_155]: (k2_relat_1(k8_relat_1(A_155, '#skF_2'))=A_155 | ~v1_relat_1('#skF_2') | ~r1_tarski(A_155, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3826, c_28])).
% 4.75/1.89  tff(c_4636, plain, (![A_167]: (k2_relat_1(k8_relat_1(A_167, '#skF_2'))=A_167 | ~r1_tarski(A_167, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3840])).
% 4.75/1.89  tff(c_30, plain, (k2_relat_1(k8_relat_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.75/1.89  tff(c_4662, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4636, c_30])).
% 4.75/1.89  tff(c_4685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_4662])).
% 4.75/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.89  
% 4.75/1.89  Inference rules
% 4.75/1.89  ----------------------
% 4.75/1.89  #Ref     : 0
% 4.75/1.89  #Sup     : 1173
% 4.75/1.89  #Fact    : 0
% 4.75/1.89  #Define  : 0
% 4.75/1.89  #Split   : 1
% 4.75/1.89  #Chain   : 0
% 4.75/1.89  #Close   : 0
% 4.75/1.89  
% 4.75/1.89  Ordering : KBO
% 4.75/1.89  
% 4.75/1.89  Simplification rules
% 4.75/1.89  ----------------------
% 4.75/1.89  #Subsume      : 260
% 4.75/1.89  #Demod        : 814
% 4.75/1.89  #Tautology    : 538
% 4.75/1.89  #SimpNegUnit  : 2
% 4.75/1.89  #BackRed      : 0
% 4.75/1.89  
% 4.75/1.89  #Partial instantiations: 0
% 4.75/1.89  #Strategies tried      : 1
% 4.75/1.89  
% 4.75/1.89  Timing (in seconds)
% 4.75/1.89  ----------------------
% 4.75/1.89  Preprocessing        : 0.28
% 4.75/1.89  Parsing              : 0.15
% 4.75/1.89  CNF conversion       : 0.02
% 4.75/1.89  Main loop            : 0.85
% 4.75/1.89  Inferencing          : 0.26
% 4.75/1.89  Reduction            : 0.36
% 4.75/1.89  Demodulation         : 0.29
% 4.75/1.89  BG Simplification    : 0.03
% 4.75/1.89  Subsumption          : 0.16
% 4.75/1.89  Abstraction          : 0.04
% 4.75/1.89  MUC search           : 0.00
% 4.75/1.89  Cooper               : 0.00
% 4.75/1.89  Total                : 1.16
% 4.75/1.89  Index Insertion      : 0.00
% 4.75/1.89  Index Deletion       : 0.00
% 4.75/1.89  Index Matching       : 0.00
% 4.75/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
