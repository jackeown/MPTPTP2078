%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [A_39] : k2_tarski(A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_925,plain,(
    ! [A_1478,B_1479,C_1480,D_1481] : k2_xboole_0(k2_tarski(A_1478,B_1479),k2_tarski(C_1480,D_1481)) = k2_enumset1(A_1478,B_1479,C_1480,D_1481) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_937,plain,(
    ! [A_39,C_1480,D_1481] : k2_xboole_0(k1_tarski(A_39),k2_tarski(C_1480,D_1481)) = k2_enumset1(A_39,A_39,C_1480,D_1481) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_925])).

tff(c_943,plain,(
    ! [A_39,C_1480,D_1481] : k2_xboole_0(k1_tarski(A_39),k2_tarski(C_1480,D_1481)) = k1_enumset1(A_39,C_1480,D_1481) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_937])).

tff(c_52,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_423,plain,(
    ! [A_1064,B_1065,C_1066,D_1067] : k2_xboole_0(k1_tarski(A_1064),k1_enumset1(B_1065,C_1066,D_1067)) = k2_enumset1(A_1064,B_1065,C_1066,D_1067) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_473,plain,(
    ! [A_1064,A_40,B_41] : k2_xboole_0(k1_tarski(A_1064),k2_tarski(A_40,B_41)) = k2_enumset1(A_1064,A_40,A_40,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_423])).

tff(c_1123,plain,(
    ! [A_1707,A_1708,B_1709] : k2_enumset1(A_1707,A_1708,A_1708,B_1709) = k1_enumset1(A_1707,A_1708,B_1709) ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_473])).

tff(c_476,plain,(
    ! [A_1112,A_1113,B_1114] : k2_xboole_0(k1_tarski(A_1112),k2_tarski(A_1113,B_1114)) = k2_enumset1(A_1112,A_1113,A_1113,B_1114) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_423])).

tff(c_764,plain,(
    ! [A_1388,A_1389] : k2_xboole_0(k1_tarski(A_1388),k1_tarski(A_1389)) = k2_enumset1(A_1388,A_1389,A_1389,A_1389) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_476])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_788,plain,(
    k2_enumset1('#skF_5','#skF_6','#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_60])).

tff(c_1133,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_788])).

tff(c_8,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1183,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_8])).

tff(c_30,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1241,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1183,c_30])).

tff(c_1275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  %$ r2_hidden > k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.87/1.43  
% 2.87/1.43  %Foreground sorts:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Background operators:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Foreground operators:
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.43  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.87/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.87/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.87/1.43  
% 2.87/1.44  tff(f_72, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.87/1.44  tff(f_65, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.87/1.44  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.44  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.87/1.44  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.87/1.44  tff(f_57, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.87/1.44  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.87/1.44  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.87/1.44  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.44  tff(c_54, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.44  tff(c_50, plain, (![A_39]: (k2_tarski(A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.44  tff(c_925, plain, (![A_1478, B_1479, C_1480, D_1481]: (k2_xboole_0(k2_tarski(A_1478, B_1479), k2_tarski(C_1480, D_1481))=k2_enumset1(A_1478, B_1479, C_1480, D_1481))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.44  tff(c_937, plain, (![A_39, C_1480, D_1481]: (k2_xboole_0(k1_tarski(A_39), k2_tarski(C_1480, D_1481))=k2_enumset1(A_39, A_39, C_1480, D_1481))), inference(superposition, [status(thm), theory('equality')], [c_50, c_925])).
% 2.87/1.44  tff(c_943, plain, (![A_39, C_1480, D_1481]: (k2_xboole_0(k1_tarski(A_39), k2_tarski(C_1480, D_1481))=k1_enumset1(A_39, C_1480, D_1481))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_937])).
% 2.87/1.44  tff(c_52, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.44  tff(c_423, plain, (![A_1064, B_1065, C_1066, D_1067]: (k2_xboole_0(k1_tarski(A_1064), k1_enumset1(B_1065, C_1066, D_1067))=k2_enumset1(A_1064, B_1065, C_1066, D_1067))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.44  tff(c_473, plain, (![A_1064, A_40, B_41]: (k2_xboole_0(k1_tarski(A_1064), k2_tarski(A_40, B_41))=k2_enumset1(A_1064, A_40, A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_52, c_423])).
% 2.87/1.44  tff(c_1123, plain, (![A_1707, A_1708, B_1709]: (k2_enumset1(A_1707, A_1708, A_1708, B_1709)=k1_enumset1(A_1707, A_1708, B_1709))), inference(demodulation, [status(thm), theory('equality')], [c_943, c_473])).
% 2.87/1.44  tff(c_476, plain, (![A_1112, A_1113, B_1114]: (k2_xboole_0(k1_tarski(A_1112), k2_tarski(A_1113, B_1114))=k2_enumset1(A_1112, A_1113, A_1113, B_1114))), inference(superposition, [status(thm), theory('equality')], [c_52, c_423])).
% 2.87/1.44  tff(c_764, plain, (![A_1388, A_1389]: (k2_xboole_0(k1_tarski(A_1388), k1_tarski(A_1389))=k2_enumset1(A_1388, A_1389, A_1389, A_1389))), inference(superposition, [status(thm), theory('equality')], [c_50, c_476])).
% 2.87/1.44  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.44  tff(c_788, plain, (k2_enumset1('#skF_5', '#skF_6', '#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_764, c_60])).
% 2.87/1.44  tff(c_1133, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1123, c_788])).
% 2.87/1.44  tff(c_8, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.87/1.44  tff(c_1183, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_8])).
% 2.87/1.44  tff(c_30, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.44  tff(c_1241, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1183, c_30])).
% 2.87/1.44  tff(c_1275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1241])).
% 2.87/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  Inference rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Ref     : 0
% 2.87/1.44  #Sup     : 147
% 2.87/1.44  #Fact    : 0
% 2.87/1.44  #Define  : 0
% 2.87/1.44  #Split   : 3
% 2.87/1.44  #Chain   : 0
% 2.87/1.44  #Close   : 0
% 2.87/1.44  
% 2.87/1.44  Ordering : KBO
% 2.87/1.44  
% 2.87/1.44  Simplification rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Subsume      : 3
% 2.87/1.44  #Demod        : 53
% 2.87/1.44  #Tautology    : 88
% 2.87/1.44  #SimpNegUnit  : 1
% 2.87/1.44  #BackRed      : 1
% 2.87/1.44  
% 2.87/1.44  #Partial instantiations: 624
% 2.87/1.44  #Strategies tried      : 1
% 2.87/1.44  
% 2.87/1.44  Timing (in seconds)
% 2.87/1.44  ----------------------
% 2.87/1.44  Preprocessing        : 0.33
% 2.87/1.44  Parsing              : 0.17
% 2.87/1.44  CNF conversion       : 0.03
% 2.87/1.44  Main loop            : 0.36
% 2.87/1.44  Inferencing          : 0.19
% 2.87/1.44  Reduction            : 0.09
% 2.87/1.44  Demodulation         : 0.06
% 2.87/1.44  BG Simplification    : 0.02
% 2.87/1.44  Subsumption          : 0.05
% 2.87/1.44  Abstraction          : 0.02
% 2.87/1.44  MUC search           : 0.00
% 2.87/1.44  Cooper               : 0.00
% 2.87/1.44  Total                : 0.71
% 2.87/1.45  Index Insertion      : 0.00
% 2.87/1.45  Index Deletion       : 0.00
% 2.87/1.45  Index Matching       : 0.00
% 2.87/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
