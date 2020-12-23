%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 109 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_56,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_58,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_284,plain,(
    ! [C_82,D_83,A_84] :
      ( r2_hidden(C_82,D_83)
      | ~ r2_hidden(D_83,A_84)
      | ~ r2_hidden(C_82,k1_setfam_1(A_84))
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_299,plain,(
    ! [C_82] :
      ( r2_hidden(C_82,'#skF_8')
      | ~ r2_hidden(C_82,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_58,c_284])).

tff(c_316,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_168,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_8',B_64)
      | ~ r1_tarski('#skF_9',B_64) ) ),
    inference(resolution,[status(thm)],[c_58,c_168])).

tff(c_32,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [B_40] : k3_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_30])).

tff(c_98,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    ! [B_40] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_98])).

tff(c_111,plain,(
    ! [B_52] : k4_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_107])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,(
    ! [D_53,B_54] :
      ( ~ r2_hidden(D_53,B_54)
      | ~ r2_hidden(D_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_127,plain,(
    ~ r2_hidden('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_58,c_124])).

tff(c_192,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_175,c_127])).

tff(c_320,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_192])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_320])).

tff(c_335,plain,(
    ! [C_87] :
      ( r2_hidden(C_87,'#skF_8')
      | ~ r2_hidden(C_87,k1_setfam_1('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_388,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_9'),B_90),'#skF_8')
      | r1_tarski(k1_setfam_1('#skF_9'),B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_335])).

tff(c_398,plain,(
    r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_388,c_4])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.41  
% 2.34/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.41  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 2.34/1.41  
% 2.34/1.41  %Foreground sorts:
% 2.34/1.41  
% 2.34/1.41  
% 2.34/1.41  %Background operators:
% 2.34/1.41  
% 2.34/1.41  
% 2.34/1.41  %Foreground operators:
% 2.34/1.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.34/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.34/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.34/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.34/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.41  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.34/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.34/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.41  
% 2.34/1.42  tff(f_76, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.34/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.34/1.42  tff(f_71, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.34/1.42  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.34/1.42  tff(f_46, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.34/1.42  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.34/1.42  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.34/1.42  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.34/1.42  tff(c_56, plain, (~r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.34/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.42  tff(c_128, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.42  tff(c_145, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_128, c_4])).
% 2.34/1.42  tff(c_58, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.34/1.42  tff(c_284, plain, (![C_82, D_83, A_84]: (r2_hidden(C_82, D_83) | ~r2_hidden(D_83, A_84) | ~r2_hidden(C_82, k1_setfam_1(A_84)) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.42  tff(c_299, plain, (![C_82]: (r2_hidden(C_82, '#skF_8') | ~r2_hidden(C_82, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_58, c_284])).
% 2.34/1.42  tff(c_316, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_299])).
% 2.34/1.42  tff(c_168, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.42  tff(c_175, plain, (![B_64]: (r2_hidden('#skF_8', B_64) | ~r1_tarski('#skF_9', B_64))), inference(resolution, [status(thm)], [c_58, c_168])).
% 2.34/1.42  tff(c_32, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.34/1.42  tff(c_74, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.42  tff(c_30, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.42  tff(c_79, plain, (![B_40]: (k3_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_30])).
% 2.34/1.42  tff(c_98, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.42  tff(c_107, plain, (![B_40]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_40))), inference(superposition, [status(thm), theory('equality')], [c_79, c_98])).
% 2.34/1.42  tff(c_111, plain, (![B_52]: (k4_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_107])).
% 2.34/1.42  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.42  tff(c_124, plain, (![D_53, B_54]: (~r2_hidden(D_53, B_54) | ~r2_hidden(D_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_111, c_10])).
% 2.34/1.42  tff(c_127, plain, (~r2_hidden('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_124])).
% 2.34/1.42  tff(c_192, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_127])).
% 2.34/1.42  tff(c_320, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_192])).
% 2.34/1.42  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_320])).
% 2.34/1.42  tff(c_335, plain, (![C_87]: (r2_hidden(C_87, '#skF_8') | ~r2_hidden(C_87, k1_setfam_1('#skF_9')))), inference(splitRight, [status(thm)], [c_299])).
% 2.34/1.42  tff(c_388, plain, (![B_90]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_9'), B_90), '#skF_8') | r1_tarski(k1_setfam_1('#skF_9'), B_90))), inference(resolution, [status(thm)], [c_6, c_335])).
% 2.34/1.42  tff(c_398, plain, (r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_388, c_4])).
% 2.34/1.42  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_398])).
% 2.34/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.42  
% 2.34/1.42  Inference rules
% 2.34/1.42  ----------------------
% 2.34/1.42  #Ref     : 0
% 2.34/1.42  #Sup     : 75
% 2.34/1.42  #Fact    : 0
% 2.34/1.42  #Define  : 0
% 2.34/1.42  #Split   : 2
% 2.34/1.42  #Chain   : 0
% 2.34/1.42  #Close   : 0
% 2.34/1.42  
% 2.34/1.42  Ordering : KBO
% 2.34/1.42  
% 2.34/1.42  Simplification rules
% 2.34/1.42  ----------------------
% 2.34/1.42  #Subsume      : 9
% 2.34/1.42  #Demod        : 30
% 2.34/1.42  #Tautology    : 26
% 2.34/1.42  #SimpNegUnit  : 3
% 2.34/1.42  #BackRed      : 13
% 2.34/1.42  
% 2.34/1.42  #Partial instantiations: 0
% 2.34/1.42  #Strategies tried      : 1
% 2.34/1.42  
% 2.34/1.42  Timing (in seconds)
% 2.34/1.42  ----------------------
% 2.34/1.42  Preprocessing        : 0.31
% 2.34/1.42  Parsing              : 0.17
% 2.34/1.42  CNF conversion       : 0.03
% 2.34/1.42  Main loop            : 0.27
% 2.34/1.42  Inferencing          : 0.09
% 2.34/1.42  Reduction            : 0.08
% 2.34/1.42  Demodulation         : 0.05
% 2.34/1.42  BG Simplification    : 0.02
% 2.34/1.43  Subsumption          : 0.07
% 2.34/1.43  Abstraction          : 0.01
% 2.34/1.43  MUC search           : 0.00
% 2.34/1.43  Cooper               : 0.00
% 2.34/1.43  Total                : 0.61
% 2.34/1.43  Index Insertion      : 0.00
% 2.34/1.43  Index Deletion       : 0.00
% 2.34/1.43  Index Matching       : 0.00
% 2.34/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
