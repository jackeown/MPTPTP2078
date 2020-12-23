%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   61 (  83 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 120 expanded)
%              Number of equality atoms :   37 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_74,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_284,plain,(
    ! [D_88,B_89,A_90] :
      ( ~ r2_hidden(D_88,B_89)
      | r2_hidden(D_88,k2_xboole_0(A_90,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_299,plain,(
    ! [D_88] :
      ( ~ r2_hidden(D_88,'#skF_8')
      | r2_hidden(D_88,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_284])).

tff(c_44,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_432,plain,(
    ! [D_101,B_102,A_103] :
      ( D_101 = B_102
      | D_101 = A_103
      | ~ r2_hidden(D_101,k2_tarski(A_103,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_451,plain,(
    ! [D_104,A_105] :
      ( D_104 = A_105
      | D_104 = A_105
      | ~ r2_hidden(D_104,k1_tarski(A_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_432])).

tff(c_474,plain,(
    ! [D_106] :
      ( D_106 = '#skF_6'
      | ~ r2_hidden(D_106,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_299,c_451])).

tff(c_478,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_474])).

tff(c_481,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_478])).

tff(c_485,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_20])).

tff(c_488,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_485])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_97,plain,(
    ! [A_59,B_60] : r1_tarski(A_59,k2_xboole_0(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_97])).

tff(c_503,plain,(
    ! [B_108,A_109] :
      ( k1_tarski(B_108) = A_109
      | k1_xboole_0 = A_109
      | ~ r1_tarski(A_109,k1_tarski(B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_510,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_100,c_503])).

tff(c_520,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_510])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k1_tarski(A_47),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_799,plain,(
    ! [B_121] :
      ( r1_tarski('#skF_7',B_121)
      | ~ r2_hidden('#skF_6',B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_60])).

tff(c_852,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_488,c_799])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_866,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_852,c_22])).

tff(c_529,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_76])).

tff(c_867,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_529])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 2.68/1.39  
% 2.68/1.39  %Foreground sorts:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Background operators:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Foreground operators:
% 2.68/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.68/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.68/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.68/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.39  
% 2.68/1.40  tff(f_96, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.68/1.40  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.68/1.40  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.68/1.40  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.68/1.40  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.68/1.40  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.68/1.40  tff(f_81, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.68/1.40  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.68/1.40  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.68/1.40  tff(c_74, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.40  tff(c_70, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.40  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.40  tff(c_76, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.40  tff(c_284, plain, (![D_88, B_89, A_90]: (~r2_hidden(D_88, B_89) | r2_hidden(D_88, k2_xboole_0(A_90, B_89)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.40  tff(c_299, plain, (![D_88]: (~r2_hidden(D_88, '#skF_8') | r2_hidden(D_88, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_284])).
% 2.68/1.40  tff(c_44, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.40  tff(c_432, plain, (![D_101, B_102, A_103]: (D_101=B_102 | D_101=A_103 | ~r2_hidden(D_101, k2_tarski(A_103, B_102)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.68/1.40  tff(c_451, plain, (![D_104, A_105]: (D_104=A_105 | D_104=A_105 | ~r2_hidden(D_104, k1_tarski(A_105)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_432])).
% 2.68/1.40  tff(c_474, plain, (![D_106]: (D_106='#skF_6' | ~r2_hidden(D_106, '#skF_8'))), inference(resolution, [status(thm)], [c_299, c_451])).
% 2.68/1.40  tff(c_478, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_474])).
% 2.68/1.40  tff(c_481, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_70, c_478])).
% 2.68/1.40  tff(c_485, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_481, c_20])).
% 2.68/1.40  tff(c_488, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_70, c_485])).
% 2.68/1.40  tff(c_72, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.40  tff(c_97, plain, (![A_59, B_60]: (r1_tarski(A_59, k2_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.40  tff(c_100, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_97])).
% 2.68/1.40  tff(c_503, plain, (![B_108, A_109]: (k1_tarski(B_108)=A_109 | k1_xboole_0=A_109 | ~r1_tarski(A_109, k1_tarski(B_108)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.40  tff(c_510, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_100, c_503])).
% 2.68/1.40  tff(c_520, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_72, c_510])).
% 2.68/1.40  tff(c_60, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.40  tff(c_799, plain, (![B_121]: (r1_tarski('#skF_7', B_121) | ~r2_hidden('#skF_6', B_121))), inference(superposition, [status(thm), theory('equality')], [c_520, c_60])).
% 2.68/1.40  tff(c_852, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_488, c_799])).
% 2.68/1.40  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.40  tff(c_866, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_852, c_22])).
% 2.68/1.40  tff(c_529, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_520, c_76])).
% 2.68/1.40  tff(c_867, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_866, c_529])).
% 2.68/1.40  tff(c_869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_867])).
% 2.68/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.40  
% 2.68/1.40  Inference rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Ref     : 0
% 2.68/1.40  #Sup     : 194
% 2.68/1.40  #Fact    : 0
% 2.68/1.40  #Define  : 0
% 2.68/1.40  #Split   : 0
% 2.68/1.40  #Chain   : 0
% 2.68/1.41  #Close   : 0
% 2.68/1.41  
% 2.68/1.41  Ordering : KBO
% 2.68/1.41  
% 2.68/1.41  Simplification rules
% 2.68/1.41  ----------------------
% 2.68/1.41  #Subsume      : 7
% 2.68/1.41  #Demod        : 84
% 2.68/1.41  #Tautology    : 129
% 2.68/1.41  #SimpNegUnit  : 6
% 2.68/1.41  #BackRed      : 6
% 2.68/1.41  
% 2.68/1.41  #Partial instantiations: 0
% 2.68/1.41  #Strategies tried      : 1
% 2.68/1.41  
% 2.68/1.41  Timing (in seconds)
% 2.68/1.41  ----------------------
% 2.68/1.41  Preprocessing        : 0.33
% 2.68/1.41  Parsing              : 0.17
% 2.68/1.41  CNF conversion       : 0.03
% 2.68/1.41  Main loop            : 0.32
% 2.68/1.41  Inferencing          : 0.11
% 2.68/1.41  Reduction            : 0.11
% 2.68/1.41  Demodulation         : 0.08
% 2.68/1.41  BG Simplification    : 0.02
% 2.68/1.41  Subsumption          : 0.05
% 2.68/1.41  Abstraction          : 0.02
% 2.68/1.41  MUC search           : 0.00
% 2.68/1.41  Cooper               : 0.00
% 2.68/1.41  Total                : 0.68
% 2.68/1.41  Index Insertion      : 0.00
% 2.68/1.41  Index Deletion       : 0.00
% 2.68/1.41  Index Matching       : 0.00
% 2.68/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
