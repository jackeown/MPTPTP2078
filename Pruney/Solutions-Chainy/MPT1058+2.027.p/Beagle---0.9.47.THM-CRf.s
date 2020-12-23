%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 ( 107 expanded)
%              Number of equality atoms :   37 (  61 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_4') != k10_relat_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_214,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [B_41] : k4_xboole_0(B_41,B_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    ! [B_42] : r1_tarski(k1_xboole_0,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_22])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_18])).

tff(c_260,plain,(
    ! [B_57] : k3_xboole_0(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_110])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_265,plain,(
    ! [B_57] : k3_xboole_0(B_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_2])).

tff(c_24,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_482,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1165,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ r1_tarski(B_105,A_106)
      | k4_xboole_0(A_106,B_105) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_482])).

tff(c_1192,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_1165])).

tff(c_1210,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = A_107
      | k3_xboole_0(A_107,B_108) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1192])).

tff(c_95,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_255,plain,(
    ! [B_9] : k4_xboole_0(B_9,k1_xboole_0) = k3_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_214])).

tff(c_1253,plain,(
    ! [A_107] :
      ( k3_xboole_0(A_107,A_107) = A_107
      | k3_xboole_0(A_107,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_255])).

tff(c_1338,plain,(
    ! [A_107] : k3_xboole_0(A_107,A_107) = A_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1253])).

tff(c_1363,plain,(
    ! [B_9] : k4_xboole_0(B_9,k1_xboole_0) = B_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_255])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,(
    k4_xboole_0(k10_relat_1('#skF_2','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_242,plain,(
    k4_xboole_0(k10_relat_1('#skF_2','#skF_4'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_214])).

tff(c_258,plain,(
    k4_xboole_0(k10_relat_1('#skF_2','#skF_4'),k1_xboole_0) = k3_xboole_0('#skF_3',k10_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_1431,plain,(
    k3_xboole_0('#skF_3',k10_relat_1('#skF_2','#skF_4')) = k10_relat_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_258])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = k10_relat_1(k7_relat_1(C_25,A_23),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2264,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_4') = k10_relat_1('#skF_2','#skF_4')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1431,c_30])).

tff(c_2303,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_4') = k10_relat_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2264])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.63  
% 3.28/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.63  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.28/1.63  
% 3.28/1.63  %Foreground sorts:
% 3.28/1.63  
% 3.28/1.63  
% 3.28/1.63  %Background operators:
% 3.28/1.63  
% 3.28/1.63  
% 3.28/1.63  %Foreground operators:
% 3.28/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.28/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.28/1.63  
% 3.69/1.64  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.69/1.64  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.69/1.64  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.69/1.64  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.69/1.64  tff(f_50, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.69/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.69/1.64  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.69/1.64  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_4')!=k10_relat_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.64  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.64  tff(c_214, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.69/1.64  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.69/1.64  tff(c_79, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.69/1.64  tff(c_96, plain, (![B_41]: (k4_xboole_0(B_41, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_79])).
% 3.69/1.64  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.69/1.64  tff(c_106, plain, (![B_42]: (r1_tarski(k1_xboole_0, B_42))), inference(superposition, [status(thm), theory('equality')], [c_96, c_22])).
% 3.69/1.64  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.69/1.64  tff(c_110, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_106, c_18])).
% 3.69/1.64  tff(c_260, plain, (![B_57]: (k3_xboole_0(k1_xboole_0, B_57)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_214, c_110])).
% 3.69/1.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.69/1.64  tff(c_265, plain, (![B_57]: (k3_xboole_0(B_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_260, c_2])).
% 3.69/1.64  tff(c_24, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.69/1.64  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.69/1.64  tff(c_482, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.69/1.64  tff(c_1165, plain, (![B_105, A_106]: (B_105=A_106 | ~r1_tarski(B_105, A_106) | k4_xboole_0(A_106, B_105)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_482])).
% 3.69/1.64  tff(c_1192, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1165])).
% 3.69/1.64  tff(c_1210, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=A_107 | k3_xboole_0(A_107, B_108)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1192])).
% 3.69/1.64  tff(c_95, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_79])).
% 3.69/1.64  tff(c_255, plain, (![B_9]: (k4_xboole_0(B_9, k1_xboole_0)=k3_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_95, c_214])).
% 3.69/1.64  tff(c_1253, plain, (![A_107]: (k3_xboole_0(A_107, A_107)=A_107 | k3_xboole_0(A_107, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1210, c_255])).
% 3.69/1.64  tff(c_1338, plain, (![A_107]: (k3_xboole_0(A_107, A_107)=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1253])).
% 3.69/1.64  tff(c_1363, plain, (![B_9]: (k4_xboole_0(B_9, k1_xboole_0)=B_9)), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_255])).
% 3.69/1.64  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.64  tff(c_93, plain, (k4_xboole_0(k10_relat_1('#skF_2', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_79])).
% 3.69/1.64  tff(c_242, plain, (k4_xboole_0(k10_relat_1('#skF_2', '#skF_4'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_2', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93, c_214])).
% 3.69/1.64  tff(c_258, plain, (k4_xboole_0(k10_relat_1('#skF_2', '#skF_4'), k1_xboole_0)=k3_xboole_0('#skF_3', k10_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_242])).
% 3.69/1.64  tff(c_1431, plain, (k3_xboole_0('#skF_3', k10_relat_1('#skF_2', '#skF_4'))=k10_relat_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1363, c_258])).
% 3.69/1.64  tff(c_30, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=k10_relat_1(k7_relat_1(C_25, A_23), B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.69/1.64  tff(c_2264, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_4')=k10_relat_1('#skF_2', '#skF_4') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1431, c_30])).
% 3.69/1.64  tff(c_2303, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_4')=k10_relat_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2264])).
% 3.69/1.64  tff(c_2305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2303])).
% 3.69/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.64  
% 3.69/1.64  Inference rules
% 3.69/1.64  ----------------------
% 3.69/1.64  #Ref     : 1
% 3.69/1.64  #Sup     : 548
% 3.69/1.64  #Fact    : 0
% 3.69/1.64  #Define  : 0
% 3.69/1.64  #Split   : 2
% 3.69/1.64  #Chain   : 0
% 3.69/1.64  #Close   : 0
% 3.69/1.64  
% 3.69/1.64  Ordering : KBO
% 3.69/1.64  
% 3.69/1.64  Simplification rules
% 3.69/1.64  ----------------------
% 3.69/1.64  #Subsume      : 75
% 3.69/1.64  #Demod        : 263
% 3.69/1.64  #Tautology    : 315
% 3.69/1.64  #SimpNegUnit  : 5
% 3.69/1.64  #BackRed      : 8
% 3.69/1.64  
% 3.69/1.64  #Partial instantiations: 0
% 3.69/1.64  #Strategies tried      : 1
% 3.69/1.64  
% 3.69/1.64  Timing (in seconds)
% 3.69/1.64  ----------------------
% 3.69/1.65  Preprocessing        : 0.31
% 3.69/1.65  Parsing              : 0.17
% 3.69/1.65  CNF conversion       : 0.02
% 3.69/1.65  Main loop            : 0.50
% 3.69/1.65  Inferencing          : 0.16
% 3.69/1.65  Reduction            : 0.19
% 3.69/1.65  Demodulation         : 0.15
% 3.69/1.65  BG Simplification    : 0.02
% 3.69/1.65  Subsumption          : 0.08
% 3.69/1.65  Abstraction          : 0.03
% 3.69/1.65  MUC search           : 0.00
% 3.69/1.65  Cooper               : 0.00
% 3.69/1.65  Total                : 0.83
% 3.69/1.65  Index Insertion      : 0.00
% 3.69/1.65  Index Deletion       : 0.00
% 3.69/1.65  Index Matching       : 0.00
% 3.69/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
