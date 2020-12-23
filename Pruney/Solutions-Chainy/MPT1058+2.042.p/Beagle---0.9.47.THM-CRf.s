%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :   69 ( 165 expanded)
%              Number of equality atoms :   31 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_42,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_193,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = B_67
      | ~ r1_tarski(k1_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_203,plain,(
    ! [B_67] :
      ( k7_relat_1(B_67,k1_relat_1(B_67)) = B_67
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_8,c_193])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_374,plain,(
    ! [A_90,B_91] :
      ( k10_relat_1(A_90,k1_relat_1(B_91)) = k1_relat_1(k5_relat_1(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_438,plain,(
    ! [A_90,A_19] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_19))) = k10_relat_1(A_90,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_374])).

tff(c_497,plain,(
    ! [A_94,A_95] :
      ( k1_relat_1(k5_relat_1(A_94,k6_relat_1(A_95))) = k10_relat_1(A_94,A_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_438])).

tff(c_526,plain,(
    ! [A_95,A_20] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_95),A_20)) = k10_relat_1(k6_relat_1(A_20),A_95)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_497])).

tff(c_533,plain,(
    ! [A_96,A_97] : k1_relat_1(k7_relat_1(k6_relat_1(A_96),A_97)) = k10_relat_1(k6_relat_1(A_97),A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_526])).

tff(c_564,plain,(
    ! [A_96] :
      ( k10_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_96))),A_96) = k1_relat_1(k6_relat_1(A_96))
      | ~ v1_relat_1(k6_relat_1(A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_533])).

tff(c_570,plain,(
    ! [A_96] : k10_relat_1(k6_relat_1(A_96),A_96) = A_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_22,c_564])).

tff(c_196,plain,(
    ! [A_19,A_68] :
      ( k7_relat_1(k6_relat_1(A_19),A_68) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_68)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_193])).

tff(c_202,plain,(
    ! [A_19,A_68] :
      ( k7_relat_1(k6_relat_1(A_19),A_68) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_196])).

tff(c_592,plain,(
    ! [A_99] : k10_relat_1(k6_relat_1(A_99),A_99) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_22,c_564])).

tff(c_34,plain,(
    ! [A_25,C_27,B_26] :
      ( k3_xboole_0(A_25,k10_relat_1(C_27,B_26)) = k10_relat_1(k7_relat_1(C_27,A_25),B_26)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_602,plain,(
    ! [A_99,A_25] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_99),A_25),A_99) = k3_xboole_0(A_25,A_99)
      | ~ v1_relat_1(k6_relat_1(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_34])).

tff(c_805,plain,(
    ! [A_103,A_104] : k10_relat_1(k7_relat_1(k6_relat_1(A_103),A_104),A_103) = k3_xboole_0(A_104,A_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_602])).

tff(c_837,plain,(
    ! [A_68,A_19] :
      ( k3_xboole_0(A_68,A_19) = k10_relat_1(k6_relat_1(A_19),A_19)
      | ~ r1_tarski(A_19,A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_805])).

tff(c_897,plain,(
    ! [A_107,A_108] :
      ( k3_xboole_0(A_107,A_108) = A_108
      | ~ r1_tarski(A_108,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_837])).

tff(c_948,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_897])).

tff(c_1066,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_34])).

tff(c_1073,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1066])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.42  
% 2.75/1.42  %Foreground sorts:
% 2.75/1.42  
% 2.75/1.42  
% 2.75/1.42  %Background operators:
% 2.75/1.42  
% 2.75/1.42  
% 2.75/1.42  %Foreground operators:
% 2.75/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.75/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.75/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.75/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.75/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.42  
% 2.75/1.44  tff(f_108, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.75/1.44  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.75/1.44  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.75/1.44  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.75/1.44  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.75/1.44  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.75/1.44  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.75/1.44  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.75/1.44  tff(c_42, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.75/1.44  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.75/1.44  tff(c_44, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.75/1.44  tff(c_30, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.75/1.44  tff(c_22, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.75/1.44  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.44  tff(c_193, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=B_67 | ~r1_tarski(k1_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.44  tff(c_203, plain, (![B_67]: (k7_relat_1(B_67, k1_relat_1(B_67))=B_67 | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_8, c_193])).
% 2.75/1.44  tff(c_26, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.75/1.44  tff(c_374, plain, (![A_90, B_91]: (k10_relat_1(A_90, k1_relat_1(B_91))=k1_relat_1(k5_relat_1(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.44  tff(c_438, plain, (![A_90, A_19]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_19)))=k10_relat_1(A_90, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_22, c_374])).
% 2.75/1.44  tff(c_497, plain, (![A_94, A_95]: (k1_relat_1(k5_relat_1(A_94, k6_relat_1(A_95)))=k10_relat_1(A_94, A_95) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_438])).
% 2.75/1.44  tff(c_526, plain, (![A_95, A_20]: (k1_relat_1(k7_relat_1(k6_relat_1(A_95), A_20))=k10_relat_1(k6_relat_1(A_20), A_95) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_497])).
% 2.75/1.44  tff(c_533, plain, (![A_96, A_97]: (k1_relat_1(k7_relat_1(k6_relat_1(A_96), A_97))=k10_relat_1(k6_relat_1(A_97), A_96))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_526])).
% 2.75/1.44  tff(c_564, plain, (![A_96]: (k10_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_96))), A_96)=k1_relat_1(k6_relat_1(A_96)) | ~v1_relat_1(k6_relat_1(A_96)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_533])).
% 2.75/1.44  tff(c_570, plain, (![A_96]: (k10_relat_1(k6_relat_1(A_96), A_96)=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_22, c_564])).
% 2.75/1.44  tff(c_196, plain, (![A_19, A_68]: (k7_relat_1(k6_relat_1(A_19), A_68)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_68) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_193])).
% 2.75/1.44  tff(c_202, plain, (![A_19, A_68]: (k7_relat_1(k6_relat_1(A_19), A_68)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_196])).
% 2.75/1.44  tff(c_592, plain, (![A_99]: (k10_relat_1(k6_relat_1(A_99), A_99)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_22, c_564])).
% 2.75/1.44  tff(c_34, plain, (![A_25, C_27, B_26]: (k3_xboole_0(A_25, k10_relat_1(C_27, B_26))=k10_relat_1(k7_relat_1(C_27, A_25), B_26) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.44  tff(c_602, plain, (![A_99, A_25]: (k10_relat_1(k7_relat_1(k6_relat_1(A_99), A_25), A_99)=k3_xboole_0(A_25, A_99) | ~v1_relat_1(k6_relat_1(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_592, c_34])).
% 2.75/1.44  tff(c_805, plain, (![A_103, A_104]: (k10_relat_1(k7_relat_1(k6_relat_1(A_103), A_104), A_103)=k3_xboole_0(A_104, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_602])).
% 2.75/1.44  tff(c_837, plain, (![A_68, A_19]: (k3_xboole_0(A_68, A_19)=k10_relat_1(k6_relat_1(A_19), A_19) | ~r1_tarski(A_19, A_68))), inference(superposition, [status(thm), theory('equality')], [c_202, c_805])).
% 2.75/1.44  tff(c_897, plain, (![A_107, A_108]: (k3_xboole_0(A_107, A_108)=A_108 | ~r1_tarski(A_108, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_570, c_837])).
% 2.75/1.44  tff(c_948, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_897])).
% 2.75/1.44  tff(c_1066, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_948, c_34])).
% 2.75/1.44  tff(c_1073, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1066])).
% 2.75/1.44  tff(c_1075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1073])).
% 2.75/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  Inference rules
% 2.75/1.44  ----------------------
% 2.75/1.44  #Ref     : 0
% 2.75/1.44  #Sup     : 224
% 2.75/1.44  #Fact    : 0
% 2.75/1.44  #Define  : 0
% 2.75/1.44  #Split   : 1
% 2.75/1.44  #Chain   : 0
% 2.75/1.44  #Close   : 0
% 2.75/1.44  
% 2.75/1.44  Ordering : KBO
% 2.75/1.44  
% 2.75/1.44  Simplification rules
% 2.75/1.44  ----------------------
% 2.75/1.44  #Subsume      : 12
% 2.75/1.44  #Demod        : 138
% 2.75/1.44  #Tautology    : 91
% 2.75/1.44  #SimpNegUnit  : 1
% 2.75/1.44  #BackRed      : 2
% 2.75/1.44  
% 2.75/1.44  #Partial instantiations: 0
% 2.75/1.44  #Strategies tried      : 1
% 2.75/1.44  
% 2.75/1.44  Timing (in seconds)
% 2.75/1.44  ----------------------
% 2.75/1.44  Preprocessing        : 0.31
% 2.75/1.44  Parsing              : 0.16
% 2.75/1.44  CNF conversion       : 0.02
% 2.75/1.44  Main loop            : 0.35
% 2.75/1.44  Inferencing          : 0.13
% 2.75/1.44  Reduction            : 0.12
% 2.75/1.44  Demodulation         : 0.09
% 2.75/1.44  BG Simplification    : 0.02
% 2.75/1.44  Subsumption          : 0.07
% 2.75/1.44  Abstraction          : 0.02
% 2.75/1.44  MUC search           : 0.00
% 2.75/1.44  Cooper               : 0.00
% 2.75/1.44  Total                : 0.70
% 2.75/1.44  Index Insertion      : 0.00
% 2.75/1.44  Index Deletion       : 0.00
% 2.75/1.44  Index Matching       : 0.00
% 2.75/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
