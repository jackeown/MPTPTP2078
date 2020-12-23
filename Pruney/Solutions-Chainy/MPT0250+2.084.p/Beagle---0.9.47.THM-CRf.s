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
% DateTime   : Thu Dec  3 09:50:43 EST 2020

% Result     : Theorem 6.56s
% Output     : CNFRefutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :   59 (  78 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 101 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_66,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_85,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ! [B_90,A_89] : r2_hidden(B_90,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_18])).

tff(c_114,plain,(
    ! [A_96,B_97] : k3_tarski(k2_tarski(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_62,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,k3_tarski(B_69))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9054,plain,(
    ! [A_15269,A_15270,B_15271] :
      ( r1_tarski(A_15269,k2_xboole_0(A_15270,B_15271))
      | ~ r2_hidden(A_15269,k2_tarski(A_15270,B_15271)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_62])).

tff(c_9077,plain,(
    ! [B_90,A_89] : r1_tarski(B_90,k2_xboole_0(A_89,B_90)) ),
    inference(resolution,[status(thm)],[c_94,c_9054])).

tff(c_68,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_156,plain,(
    ! [A_103,B_104] :
      ( r2_xboole_0(A_103,B_104)
      | B_104 = A_103
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    ! [B_106,A_107] :
      ( ~ r1_tarski(B_106,A_107)
      | B_106 = A_107
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_184,plain,
    ( k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_172])).

tff(c_338,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_9082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9077,c_338])).

tff(c_9083,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_64,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_22])).

tff(c_48,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_22])).

tff(c_106,plain,(
    ! [A_40] : r2_hidden(A_40,k1_tarski(A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_103])).

tff(c_194,plain,(
    ! [C_111,B_112,A_113] :
      ( r2_hidden(C_111,B_112)
      | ~ r2_hidden(C_111,A_113)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_216,plain,(
    ! [A_114,B_115] :
      ( r2_hidden(A_114,B_115)
      | ~ r1_tarski(k1_tarski(A_114),B_115) ) ),
    inference(resolution,[status(thm)],[c_106,c_194])).

tff(c_305,plain,(
    ! [A_126,B_127] :
      ( r2_hidden(A_126,k3_tarski(B_127))
      | ~ r2_hidden(k1_tarski(A_126),B_127) ) ),
    inference(resolution,[status(thm)],[c_62,c_216])).

tff(c_317,plain,(
    ! [A_126,B_90] : r2_hidden(A_126,k3_tarski(k2_tarski(k1_tarski(A_126),B_90))) ),
    inference(resolution,[status(thm)],[c_91,c_305])).

tff(c_9182,plain,(
    ! [A_15426,B_15427] : r2_hidden(A_15426,k2_xboole_0(k1_tarski(A_15426),B_15427)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_317])).

tff(c_9191,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9083,c_9182])).

tff(c_9199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:49:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.56/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.35  
% 6.56/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.35  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.56/2.35  
% 6.56/2.35  %Foreground sorts:
% 6.56/2.35  
% 6.56/2.35  
% 6.56/2.35  %Background operators:
% 6.56/2.35  
% 6.56/2.35  
% 6.56/2.35  %Foreground operators:
% 6.56/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.56/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.56/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.56/2.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.56/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.56/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.56/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.56/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.56/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.56/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.56/2.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.56/2.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.56/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.56/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.56/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.56/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.56/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.56/2.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.56/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.56/2.35  
% 6.56/2.37  tff(f_92, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 6.56/2.37  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.56/2.37  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.56/2.37  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.56/2.37  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.56/2.37  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.56/2.37  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 6.56/2.37  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.56/2.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.56/2.37  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.56/2.37  tff(c_85, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.56/2.37  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.56/2.37  tff(c_94, plain, (![B_90, A_89]: (r2_hidden(B_90, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_18])).
% 6.56/2.37  tff(c_114, plain, (![A_96, B_97]: (k3_tarski(k2_tarski(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.56/2.37  tff(c_62, plain, (![A_68, B_69]: (r1_tarski(A_68, k3_tarski(B_69)) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.56/2.37  tff(c_9054, plain, (![A_15269, A_15270, B_15271]: (r1_tarski(A_15269, k2_xboole_0(A_15270, B_15271)) | ~r2_hidden(A_15269, k2_tarski(A_15270, B_15271)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_62])).
% 6.56/2.37  tff(c_9077, plain, (![B_90, A_89]: (r1_tarski(B_90, k2_xboole_0(A_89, B_90)))), inference(resolution, [status(thm)], [c_94, c_9054])).
% 6.56/2.37  tff(c_68, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.56/2.37  tff(c_156, plain, (![A_103, B_104]: (r2_xboole_0(A_103, B_104) | B_104=A_103 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.56/2.37  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.56/2.37  tff(c_172, plain, (![B_106, A_107]: (~r1_tarski(B_106, A_107) | B_106=A_107 | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_156, c_14])).
% 6.56/2.37  tff(c_184, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_172])).
% 6.56/2.37  tff(c_338, plain, (~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_184])).
% 6.56/2.37  tff(c_9082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9077, c_338])).
% 6.56/2.37  tff(c_9083, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_184])).
% 6.56/2.37  tff(c_64, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.56/2.37  tff(c_22, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.56/2.37  tff(c_91, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_22])).
% 6.56/2.37  tff(c_48, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.56/2.37  tff(c_103, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_22])).
% 6.56/2.37  tff(c_106, plain, (![A_40]: (r2_hidden(A_40, k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_103])).
% 6.56/2.37  tff(c_194, plain, (![C_111, B_112, A_113]: (r2_hidden(C_111, B_112) | ~r2_hidden(C_111, A_113) | ~r1_tarski(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.56/2.37  tff(c_216, plain, (![A_114, B_115]: (r2_hidden(A_114, B_115) | ~r1_tarski(k1_tarski(A_114), B_115))), inference(resolution, [status(thm)], [c_106, c_194])).
% 6.56/2.37  tff(c_305, plain, (![A_126, B_127]: (r2_hidden(A_126, k3_tarski(B_127)) | ~r2_hidden(k1_tarski(A_126), B_127))), inference(resolution, [status(thm)], [c_62, c_216])).
% 6.56/2.37  tff(c_317, plain, (![A_126, B_90]: (r2_hidden(A_126, k3_tarski(k2_tarski(k1_tarski(A_126), B_90))))), inference(resolution, [status(thm)], [c_91, c_305])).
% 6.56/2.37  tff(c_9182, plain, (![A_15426, B_15427]: (r2_hidden(A_15426, k2_xboole_0(k1_tarski(A_15426), B_15427)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_317])).
% 6.56/2.37  tff(c_9191, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9083, c_9182])).
% 6.56/2.37  tff(c_9199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_9191])).
% 6.56/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.37  
% 6.56/2.37  Inference rules
% 6.56/2.37  ----------------------
% 6.56/2.37  #Ref     : 0
% 6.56/2.37  #Sup     : 1189
% 6.56/2.37  #Fact    : 18
% 6.56/2.37  #Define  : 0
% 6.56/2.37  #Split   : 1
% 6.56/2.37  #Chain   : 0
% 6.56/2.37  #Close   : 0
% 6.56/2.37  
% 6.56/2.37  Ordering : KBO
% 6.56/2.37  
% 6.56/2.37  Simplification rules
% 6.56/2.37  ----------------------
% 6.56/2.37  #Subsume      : 172
% 6.56/2.37  #Demod        : 584
% 6.56/2.37  #Tautology    : 540
% 6.56/2.37  #SimpNegUnit  : 1
% 6.56/2.37  #BackRed      : 2
% 6.56/2.37  
% 6.56/2.37  #Partial instantiations: 4590
% 6.56/2.37  #Strategies tried      : 1
% 6.56/2.37  
% 6.56/2.37  Timing (in seconds)
% 6.56/2.37  ----------------------
% 6.56/2.37  Preprocessing        : 0.34
% 6.56/2.37  Parsing              : 0.18
% 6.56/2.37  CNF conversion       : 0.03
% 6.56/2.37  Main loop            : 1.25
% 6.56/2.37  Inferencing          : 0.66
% 6.56/2.37  Reduction            : 0.35
% 6.56/2.37  Demodulation         : 0.28
% 6.56/2.37  BG Simplification    : 0.05
% 6.56/2.37  Subsumption          : 0.14
% 6.56/2.37  Abstraction          : 0.05
% 6.56/2.37  MUC search           : 0.00
% 6.56/2.37  Cooper               : 0.00
% 6.56/2.37  Total                : 1.61
% 6.87/2.37  Index Insertion      : 0.00
% 6.87/2.37  Index Deletion       : 0.00
% 6.87/2.37  Index Matching       : 0.00
% 6.87/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
