%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:39 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 (  92 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_52,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    r1_setfam_1('#skF_3',k1_tarski('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_36] : k3_tarski(k1_tarski(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k3_tarski(A_50),k3_tarski(B_51))
      | ~ r1_setfam_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    ! [A_50,A_36] :
      ( r1_tarski(k3_tarski(A_50),A_36)
      | ~ r1_setfam_1(A_50,k1_tarski(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_73,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_22,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,k3_tarski(B_35))
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_237,plain,(
    ! [A_110,B_111,B_112,B_113] :
      ( r2_hidden('#skF_1'(A_110,B_111),B_112)
      | ~ r1_tarski(B_113,B_112)
      | ~ r1_tarski(A_110,B_113)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_269,plain,(
    ! [A_123,B_124,B_125,A_126] :
      ( r2_hidden('#skF_1'(A_123,B_124),k3_tarski(B_125))
      | ~ r1_tarski(A_123,A_126)
      | r1_tarski(A_123,B_124)
      | ~ r2_hidden(A_126,B_125) ) ),
    inference(resolution,[status(thm)],[c_22,c_237])).

tff(c_291,plain,(
    ! [A_127,B_128,B_129] :
      ( r2_hidden('#skF_1'(A_127,B_128),k3_tarski(B_129))
      | r1_tarski(A_127,B_128)
      | ~ r2_hidden(A_127,B_129) ) ),
    inference(resolution,[status(thm)],[c_82,c_269])).

tff(c_342,plain,(
    ! [A_141,B_142,B_143,B_144] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_143)
      | ~ r1_tarski(k3_tarski(B_144),B_143)
      | r1_tarski(A_141,B_142)
      | ~ r2_hidden(A_141,B_144) ) ),
    inference(resolution,[status(thm)],[c_291,c_2])).

tff(c_394,plain,(
    ! [A_156,B_157,A_158,A_159] :
      ( r2_hidden('#skF_1'(A_156,B_157),A_158)
      | r1_tarski(A_156,B_157)
      | ~ r2_hidden(A_156,A_159)
      | ~ r1_setfam_1(A_159,k1_tarski(A_158)) ) ),
    inference(resolution,[status(thm)],[c_72,c_342])).

tff(c_413,plain,(
    ! [B_160,A_161] :
      ( r2_hidden('#skF_1'('#skF_4',B_160),A_161)
      | r1_tarski('#skF_4',B_160)
      | ~ r1_setfam_1('#skF_3',k1_tarski(A_161)) ) ),
    inference(resolution,[status(thm)],[c_30,c_394])).

tff(c_437,plain,(
    ! [A_162] :
      ( r1_tarski('#skF_4',A_162)
      | ~ r1_setfam_1('#skF_3',k1_tarski(A_162)) ) ),
    inference(resolution,[status(thm)],[c_413,c_4])).

tff(c_440,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_437])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.83/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.44  
% 2.83/1.46  tff(f_64, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.83/1.46  tff(f_52, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.83/1.46  tff(f_56, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.83/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.83/1.46  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.83/1.46  tff(c_28, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.46  tff(c_32, plain, (r1_setfam_1('#skF_3', k1_tarski('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.46  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.46  tff(c_24, plain, (![A_36]: (k3_tarski(k1_tarski(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.46  tff(c_66, plain, (![A_50, B_51]: (r1_tarski(k3_tarski(A_50), k3_tarski(B_51)) | ~r1_setfam_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.46  tff(c_72, plain, (![A_50, A_36]: (r1_tarski(k3_tarski(A_50), A_36) | ~r1_setfam_1(A_50, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_66])).
% 2.83/1.46  tff(c_73, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.46  tff(c_82, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_73, c_4])).
% 2.83/1.46  tff(c_22, plain, (![A_34, B_35]: (r1_tarski(A_34, k3_tarski(B_35)) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.46  tff(c_103, plain, (![C_64, B_65, A_66]: (r2_hidden(C_64, B_65) | ~r2_hidden(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.46  tff(c_160, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_6, c_103])).
% 2.83/1.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.46  tff(c_237, plain, (![A_110, B_111, B_112, B_113]: (r2_hidden('#skF_1'(A_110, B_111), B_112) | ~r1_tarski(B_113, B_112) | ~r1_tarski(A_110, B_113) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_160, c_2])).
% 2.83/1.46  tff(c_269, plain, (![A_123, B_124, B_125, A_126]: (r2_hidden('#skF_1'(A_123, B_124), k3_tarski(B_125)) | ~r1_tarski(A_123, A_126) | r1_tarski(A_123, B_124) | ~r2_hidden(A_126, B_125))), inference(resolution, [status(thm)], [c_22, c_237])).
% 2.83/1.46  tff(c_291, plain, (![A_127, B_128, B_129]: (r2_hidden('#skF_1'(A_127, B_128), k3_tarski(B_129)) | r1_tarski(A_127, B_128) | ~r2_hidden(A_127, B_129))), inference(resolution, [status(thm)], [c_82, c_269])).
% 2.83/1.46  tff(c_342, plain, (![A_141, B_142, B_143, B_144]: (r2_hidden('#skF_1'(A_141, B_142), B_143) | ~r1_tarski(k3_tarski(B_144), B_143) | r1_tarski(A_141, B_142) | ~r2_hidden(A_141, B_144))), inference(resolution, [status(thm)], [c_291, c_2])).
% 2.83/1.46  tff(c_394, plain, (![A_156, B_157, A_158, A_159]: (r2_hidden('#skF_1'(A_156, B_157), A_158) | r1_tarski(A_156, B_157) | ~r2_hidden(A_156, A_159) | ~r1_setfam_1(A_159, k1_tarski(A_158)))), inference(resolution, [status(thm)], [c_72, c_342])).
% 2.83/1.46  tff(c_413, plain, (![B_160, A_161]: (r2_hidden('#skF_1'('#skF_4', B_160), A_161) | r1_tarski('#skF_4', B_160) | ~r1_setfam_1('#skF_3', k1_tarski(A_161)))), inference(resolution, [status(thm)], [c_30, c_394])).
% 2.83/1.46  tff(c_437, plain, (![A_162]: (r1_tarski('#skF_4', A_162) | ~r1_setfam_1('#skF_3', k1_tarski(A_162)))), inference(resolution, [status(thm)], [c_413, c_4])).
% 2.83/1.46  tff(c_440, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_437])).
% 2.83/1.46  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_440])).
% 2.83/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.46  
% 2.83/1.46  Inference rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Ref     : 0
% 2.83/1.46  #Sup     : 103
% 2.83/1.46  #Fact    : 0
% 2.83/1.46  #Define  : 0
% 2.83/1.46  #Split   : 3
% 2.83/1.46  #Chain   : 0
% 2.83/1.46  #Close   : 0
% 2.83/1.46  
% 2.83/1.46  Ordering : KBO
% 2.83/1.46  
% 2.83/1.46  Simplification rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Subsume      : 11
% 2.83/1.46  #Demod        : 2
% 2.83/1.46  #Tautology    : 17
% 2.83/1.46  #SimpNegUnit  : 1
% 2.83/1.46  #BackRed      : 0
% 2.83/1.46  
% 2.83/1.46  #Partial instantiations: 0
% 2.83/1.46  #Strategies tried      : 1
% 2.83/1.46  
% 2.83/1.46  Timing (in seconds)
% 2.83/1.46  ----------------------
% 2.83/1.46  Preprocessing        : 0.31
% 2.83/1.46  Parsing              : 0.17
% 2.83/1.46  CNF conversion       : 0.02
% 2.83/1.46  Main loop            : 0.38
% 2.83/1.46  Inferencing          : 0.14
% 2.83/1.46  Reduction            : 0.09
% 2.83/1.46  Demodulation         : 0.06
% 2.83/1.46  BG Simplification    : 0.02
% 2.83/1.46  Subsumption          : 0.10
% 2.83/1.46  Abstraction          : 0.02
% 2.83/1.46  MUC search           : 0.00
% 2.83/1.46  Cooper               : 0.00
% 2.83/1.46  Total                : 0.72
% 2.83/1.46  Index Insertion      : 0.00
% 2.83/1.46  Index Deletion       : 0.00
% 2.83/1.46  Index Matching       : 0.00
% 2.83/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
