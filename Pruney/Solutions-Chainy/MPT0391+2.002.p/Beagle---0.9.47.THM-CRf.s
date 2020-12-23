%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:15 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 126 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_80,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_44,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_178,plain,(
    ! [C_59,D_60,A_61] :
      ( r2_hidden(C_59,D_60)
      | ~ r2_hidden(D_60,A_61)
      | ~ r2_hidden(C_59,k1_setfam_1(A_61))
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_187,plain,(
    ! [C_59] :
      ( r2_hidden(C_59,'#skF_6')
      | ~ r2_hidden(C_59,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_48,c_178])).

tff(c_188,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,B_52)
      | ~ r2_hidden(C_53,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    ! [C_53,B_2,A_1] :
      ( ~ r2_hidden(C_53,B_2)
      | ~ r2_hidden(C_53,A_1)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_291,plain,(
    ! [C_74,B_75,A_76] :
      ( ~ r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | k3_xboole_0(A_76,B_75) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_138])).

tff(c_304,plain,(
    ! [A_77] :
      ( ~ r2_hidden('#skF_6',A_77)
      | k3_xboole_0(A_77,'#skF_7') != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_48,c_291])).

tff(c_307,plain,(
    k3_xboole_0('#skF_7','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_48,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_307])).

tff(c_328,plain,(
    ! [C_80] :
      ( r2_hidden(C_80,'#skF_6')
      | ~ r2_hidden(C_80,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_506,plain,(
    ! [B_104] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_7'),B_104),'#skF_6')
      | r1_xboole_0(k1_setfam_1('#skF_7'),B_104) ) ),
    inference(resolution,[status(thm)],[c_12,c_328])).

tff(c_46,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_140,plain,(
    ! [C_53] :
      ( ~ r2_hidden(C_53,'#skF_8')
      | ~ r2_hidden(C_53,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_563,plain,(
    ! [B_112] :
      ( ~ r2_hidden('#skF_1'(k1_setfam_1('#skF_7'),B_112),'#skF_8')
      | r1_xboole_0(k1_setfam_1('#skF_7'),B_112) ) ),
    inference(resolution,[status(thm)],[c_506,c_140])).

tff(c_567,plain,(
    r1_xboole_0(k1_setfam_1('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_563])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n019.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:07:22 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.39  
% 2.54/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 2.54/1.39  
% 2.54/1.39  %Foreground sorts:
% 2.54/1.39  
% 2.54/1.39  
% 2.54/1.39  %Background operators:
% 2.54/1.39  
% 2.54/1.39  
% 2.54/1.39  %Foreground operators:
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.54/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.39  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.54/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.54/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.39  
% 2.54/1.41  tff(f_87, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 2.54/1.41  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.54/1.41  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.54/1.41  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.54/1.41  tff(f_80, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.54/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.54/1.41  tff(c_44, plain, (~r1_xboole_0(k1_setfam_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.54/1.41  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.41  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.41  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.41  tff(c_64, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.54/1.41  tff(c_68, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_18, c_64])).
% 2.54/1.41  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.54/1.41  tff(c_178, plain, (![C_59, D_60, A_61]: (r2_hidden(C_59, D_60) | ~r2_hidden(D_60, A_61) | ~r2_hidden(C_59, k1_setfam_1(A_61)) | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.41  tff(c_187, plain, (![C_59]: (r2_hidden(C_59, '#skF_6') | ~r2_hidden(C_59, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_48, c_178])).
% 2.54/1.41  tff(c_188, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_187])).
% 2.54/1.41  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.41  tff(c_128, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, B_52) | ~r2_hidden(C_53, A_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.41  tff(c_138, plain, (![C_53, B_2, A_1]: (~r2_hidden(C_53, B_2) | ~r2_hidden(C_53, A_1) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.54/1.41  tff(c_291, plain, (![C_74, B_75, A_76]: (~r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | k3_xboole_0(A_76, B_75)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_138])).
% 2.54/1.41  tff(c_304, plain, (![A_77]: (~r2_hidden('#skF_6', A_77) | k3_xboole_0(A_77, '#skF_7')!='#skF_7')), inference(resolution, [status(thm)], [c_48, c_291])).
% 2.54/1.41  tff(c_307, plain, (k3_xboole_0('#skF_7', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_48, c_304])).
% 2.54/1.41  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_307])).
% 2.54/1.41  tff(c_328, plain, (![C_80]: (r2_hidden(C_80, '#skF_6') | ~r2_hidden(C_80, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_187])).
% 2.54/1.41  tff(c_506, plain, (![B_104]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_7'), B_104), '#skF_6') | r1_xboole_0(k1_setfam_1('#skF_7'), B_104))), inference(resolution, [status(thm)], [c_12, c_328])).
% 2.54/1.41  tff(c_46, plain, (r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.54/1.41  tff(c_140, plain, (![C_53]: (~r2_hidden(C_53, '#skF_8') | ~r2_hidden(C_53, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_128])).
% 2.54/1.41  tff(c_563, plain, (![B_112]: (~r2_hidden('#skF_1'(k1_setfam_1('#skF_7'), B_112), '#skF_8') | r1_xboole_0(k1_setfam_1('#skF_7'), B_112))), inference(resolution, [status(thm)], [c_506, c_140])).
% 2.54/1.41  tff(c_567, plain, (r1_xboole_0(k1_setfam_1('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_10, c_563])).
% 2.54/1.41  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_567])).
% 2.54/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.41  
% 2.54/1.41  Inference rules
% 2.54/1.41  ----------------------
% 2.54/1.41  #Ref     : 0
% 2.54/1.41  #Sup     : 122
% 2.54/1.41  #Fact    : 0
% 2.54/1.41  #Define  : 0
% 2.54/1.41  #Split   : 2
% 2.54/1.41  #Chain   : 0
% 2.54/1.41  #Close   : 0
% 2.54/1.41  
% 2.54/1.41  Ordering : KBO
% 2.54/1.41  
% 2.54/1.41  Simplification rules
% 2.54/1.41  ----------------------
% 2.54/1.41  #Subsume      : 16
% 2.54/1.41  #Demod        : 66
% 2.54/1.41  #Tautology    : 51
% 2.54/1.41  #SimpNegUnit  : 4
% 2.54/1.41  #BackRed      : 25
% 2.54/1.41  
% 2.54/1.41  #Partial instantiations: 0
% 2.54/1.41  #Strategies tried      : 1
% 2.54/1.41  
% 2.54/1.41  Timing (in seconds)
% 2.54/1.41  ----------------------
% 2.54/1.41  Preprocessing        : 0.30
% 2.54/1.41  Parsing              : 0.17
% 2.54/1.41  CNF conversion       : 0.02
% 2.54/1.41  Main loop            : 0.30
% 2.54/1.41  Inferencing          : 0.11
% 2.54/1.41  Reduction            : 0.08
% 2.54/1.41  Demodulation         : 0.06
% 2.54/1.41  BG Simplification    : 0.02
% 2.54/1.41  Subsumption          : 0.07
% 2.54/1.41  Abstraction          : 0.01
% 2.54/1.41  MUC search           : 0.00
% 2.54/1.41  Cooper               : 0.00
% 2.54/1.41  Total                : 0.64
% 2.54/1.41  Index Insertion      : 0.00
% 2.54/1.41  Index Deletion       : 0.00
% 2.54/1.41  Index Matching       : 0.00
% 2.54/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
