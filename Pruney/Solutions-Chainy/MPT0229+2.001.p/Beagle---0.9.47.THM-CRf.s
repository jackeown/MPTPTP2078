%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   32 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :   38 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_172,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_172])).

tff(c_191,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_200,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_191])).

tff(c_203,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_200])).

tff(c_208,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_208])).

tff(c_220,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6,c_217])).

tff(c_128,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [B_63,A_62] : r2_hidden(B_63,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_16])).

tff(c_224,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_137])).

tff(c_40,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_250,plain,(
    ! [E_84,C_85,B_86,A_87] :
      ( E_84 = C_85
      | E_84 = B_86
      | E_84 = A_87
      | ~ r2_hidden(E_84,k1_enumset1(A_87,B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_269,plain,(
    ! [E_88,B_89,A_90] :
      ( E_88 = B_89
      | E_88 = A_90
      | E_88 = A_90
      | ~ r2_hidden(E_88,k2_tarski(A_90,B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_250])).

tff(c_292,plain,(
    ! [E_91,A_92] :
      ( E_91 = A_92
      | E_91 = A_92
      | E_91 = A_92
      | ~ r2_hidden(E_91,k1_tarski(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_269])).

tff(c_295,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_224,c_292])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.37  
% 1.98/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.98/1.37  
% 1.98/1.37  %Foreground sorts:
% 1.98/1.37  
% 1.98/1.37  
% 1.98/1.37  %Background operators:
% 1.98/1.37  
% 1.98/1.37  
% 1.98/1.37  %Foreground operators:
% 1.98/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.98/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.37  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.37  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.98/1.37  
% 2.16/1.39  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.16/1.39  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.16/1.39  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.16/1.39  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.16/1.39  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.39  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.39  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.16/1.39  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.16/1.39  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.16/1.39  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.16/1.39  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.16/1.39  tff(c_38, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.39  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.39  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.39  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.16/1.39  tff(c_172, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.39  tff(c_176, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_172])).
% 2.16/1.39  tff(c_191, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.39  tff(c_200, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_191])).
% 2.16/1.39  tff(c_203, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_200])).
% 2.16/1.39  tff(c_208, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.39  tff(c_217, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_208])).
% 2.16/1.39  tff(c_220, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6, c_217])).
% 2.16/1.39  tff(c_128, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.39  tff(c_16, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.39  tff(c_137, plain, (![B_63, A_62]: (r2_hidden(B_63, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_16])).
% 2.16/1.39  tff(c_224, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_137])).
% 2.16/1.39  tff(c_40, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.39  tff(c_42, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.39  tff(c_250, plain, (![E_84, C_85, B_86, A_87]: (E_84=C_85 | E_84=B_86 | E_84=A_87 | ~r2_hidden(E_84, k1_enumset1(A_87, B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.39  tff(c_269, plain, (![E_88, B_89, A_90]: (E_88=B_89 | E_88=A_90 | E_88=A_90 | ~r2_hidden(E_88, k2_tarski(A_90, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_250])).
% 2.16/1.39  tff(c_292, plain, (![E_91, A_92]: (E_91=A_92 | E_91=A_92 | E_91=A_92 | ~r2_hidden(E_91, k1_tarski(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_269])).
% 2.16/1.39  tff(c_295, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_224, c_292])).
% 2.16/1.39  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_295])).
% 2.16/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.39  
% 2.16/1.39  Inference rules
% 2.16/1.39  ----------------------
% 2.16/1.39  #Ref     : 0
% 2.16/1.39  #Sup     : 60
% 2.16/1.39  #Fact    : 0
% 2.16/1.39  #Define  : 0
% 2.16/1.39  #Split   : 0
% 2.16/1.39  #Chain   : 0
% 2.16/1.39  #Close   : 0
% 2.16/1.39  
% 2.16/1.39  Ordering : KBO
% 2.16/1.39  
% 2.16/1.39  Simplification rules
% 2.16/1.39  ----------------------
% 2.16/1.39  #Subsume      : 0
% 2.16/1.39  #Demod        : 10
% 2.16/1.39  #Tautology    : 46
% 2.16/1.39  #SimpNegUnit  : 1
% 2.16/1.39  #BackRed      : 0
% 2.16/1.39  
% 2.16/1.39  #Partial instantiations: 0
% 2.16/1.39  #Strategies tried      : 1
% 2.16/1.39  
% 2.16/1.39  Timing (in seconds)
% 2.16/1.39  ----------------------
% 2.16/1.39  Preprocessing        : 0.31
% 2.16/1.39  Parsing              : 0.16
% 2.16/1.39  CNF conversion       : 0.02
% 2.16/1.39  Main loop            : 0.17
% 2.16/1.39  Inferencing          : 0.06
% 2.16/1.39  Reduction            : 0.06
% 2.16/1.39  Demodulation         : 0.05
% 2.16/1.39  BG Simplification    : 0.01
% 2.16/1.39  Subsumption          : 0.03
% 2.16/1.39  Abstraction          : 0.01
% 2.16/1.39  MUC search           : 0.00
% 2.16/1.39  Cooper               : 0.00
% 2.16/1.39  Total                : 0.51
% 2.16/1.39  Index Insertion      : 0.00
% 2.16/1.39  Index Deletion       : 0.00
% 2.16/1.39  Index Matching       : 0.00
% 2.16/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
