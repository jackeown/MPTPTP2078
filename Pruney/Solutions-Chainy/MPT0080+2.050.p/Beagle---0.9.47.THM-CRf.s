%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   46 (  75 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 178 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
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

tff(c_32,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_889,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden('#skF_2'(A_135,B_136,C_137),B_136)
      | r2_hidden('#skF_2'(A_135,B_136,C_137),A_135)
      | r2_hidden('#skF_3'(A_135,B_136,C_137),C_137)
      | k2_xboole_0(A_135,B_136) = C_137 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3430,plain,(
    ! [A_338,B_339] :
      ( r2_hidden('#skF_2'(A_338,B_339,B_339),A_338)
      | r2_hidden('#skF_3'(A_338,B_339,B_339),B_339)
      | k2_xboole_0(A_338,B_339) = B_339 ) ),
    inference(resolution,[status(thm)],[c_889,c_22])).

tff(c_650,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_2'(A_117,B_118,C_119),B_118)
      | r2_hidden('#skF_2'(A_117,B_118,C_119),A_117)
      | ~ r2_hidden('#skF_3'(A_117,B_118,C_119),B_118)
      | k2_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | k2_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_722,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_2'(A_117,B_118,B_118),A_117)
      | ~ r2_hidden('#skF_3'(A_117,B_118,B_118),B_118)
      | k2_xboole_0(A_117,B_118) = B_118 ) ),
    inference(resolution,[status(thm)],[c_650,c_14])).

tff(c_3557,plain,(
    ! [A_342,B_343] :
      ( r2_hidden('#skF_2'(A_342,B_343,B_343),A_342)
      | k2_xboole_0(A_342,B_343) = B_343 ) ),
    inference(resolution,[status(thm)],[c_3430,c_722])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3821,plain,(
    ! [A_354,B_355,B_356] :
      ( r2_hidden('#skF_2'(A_354,B_355,B_355),B_356)
      | ~ r1_tarski(A_354,B_356)
      | k2_xboole_0(A_354,B_355) = B_355 ) ),
    inference(resolution,[status(thm)],[c_3557,c_2])).

tff(c_4296,plain,(
    ! [A_382,B_383] :
      ( r2_hidden('#skF_3'(A_382,B_383,B_383),B_383)
      | ~ r1_tarski(A_382,B_383)
      | k2_xboole_0(A_382,B_383) = B_383 ) ),
    inference(resolution,[status(thm)],[c_3821,c_22])).

tff(c_3919,plain,(
    ! [A_354,B_356] :
      ( ~ r2_hidden('#skF_3'(A_354,B_356,B_356),B_356)
      | ~ r1_tarski(A_354,B_356)
      | k2_xboole_0(A_354,B_356) = B_356 ) ),
    inference(resolution,[status(thm)],[c_3821,c_14])).

tff(c_4361,plain,(
    ! [A_384,B_385] :
      ( ~ r1_tarski(A_384,B_385)
      | k2_xboole_0(A_384,B_385) = B_385 ) ),
    inference(resolution,[status(thm)],[c_4296,c_3919])).

tff(c_4386,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_4361])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5133,plain,(
    ! [D_393] :
      ( ~ r2_hidden(D_393,'#skF_5')
      | r2_hidden(D_393,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4386,c_12])).

tff(c_8,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5227,plain,(
    ! [D_394] :
      ( r2_hidden(D_394,'#skF_7')
      | r2_hidden(D_394,'#skF_6')
      | ~ r2_hidden(D_394,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5133,c_8])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,B_36)
      | ~ r2_hidden(C_37,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_7')
      | ~ r2_hidden(C_37,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_75])).

tff(c_5352,plain,(
    ! [D_395] :
      ( r2_hidden(D_395,'#skF_6')
      | ~ r2_hidden(D_395,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5227,c_78])).

tff(c_5486,plain,(
    ! [B_397] :
      ( r2_hidden('#skF_1'('#skF_5',B_397),'#skF_6')
      | r1_tarski('#skF_5',B_397) ) ),
    inference(resolution,[status(thm)],[c_6,c_5352])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5519,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_5486,c_4])).

tff(c_5535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_5519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.41  
% 7.02/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.10/2.41  
% 7.10/2.41  %Foreground sorts:
% 7.10/2.41  
% 7.10/2.41  
% 7.10/2.41  %Background operators:
% 7.10/2.41  
% 7.10/2.41  
% 7.10/2.41  %Foreground operators:
% 7.10/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.10/2.41  tff('#skF_7', type, '#skF_7': $i).
% 7.10/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.10/2.41  tff('#skF_5', type, '#skF_5': $i).
% 7.10/2.41  tff('#skF_6', type, '#skF_6': $i).
% 7.10/2.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.10/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.10/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.10/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.10/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.10/2.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.10/2.41  
% 7.10/2.43  tff(f_66, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.10/2.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.10/2.43  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.10/2.43  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.10/2.43  tff(c_32, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.10/2.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.43  tff(c_36, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.10/2.43  tff(c_889, plain, (![A_135, B_136, C_137]: (r2_hidden('#skF_2'(A_135, B_136, C_137), B_136) | r2_hidden('#skF_2'(A_135, B_136, C_137), A_135) | r2_hidden('#skF_3'(A_135, B_136, C_137), C_137) | k2_xboole_0(A_135, B_136)=C_137)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.43  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.43  tff(c_3430, plain, (![A_338, B_339]: (r2_hidden('#skF_2'(A_338, B_339, B_339), A_338) | r2_hidden('#skF_3'(A_338, B_339, B_339), B_339) | k2_xboole_0(A_338, B_339)=B_339)), inference(resolution, [status(thm)], [c_889, c_22])).
% 7.10/2.43  tff(c_650, plain, (![A_117, B_118, C_119]: (r2_hidden('#skF_2'(A_117, B_118, C_119), B_118) | r2_hidden('#skF_2'(A_117, B_118, C_119), A_117) | ~r2_hidden('#skF_3'(A_117, B_118, C_119), B_118) | k2_xboole_0(A_117, B_118)=C_119)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.43  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | k2_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.43  tff(c_722, plain, (![A_117, B_118]: (r2_hidden('#skF_2'(A_117, B_118, B_118), A_117) | ~r2_hidden('#skF_3'(A_117, B_118, B_118), B_118) | k2_xboole_0(A_117, B_118)=B_118)), inference(resolution, [status(thm)], [c_650, c_14])).
% 7.10/2.43  tff(c_3557, plain, (![A_342, B_343]: (r2_hidden('#skF_2'(A_342, B_343, B_343), A_342) | k2_xboole_0(A_342, B_343)=B_343)), inference(resolution, [status(thm)], [c_3430, c_722])).
% 7.10/2.43  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.43  tff(c_3821, plain, (![A_354, B_355, B_356]: (r2_hidden('#skF_2'(A_354, B_355, B_355), B_356) | ~r1_tarski(A_354, B_356) | k2_xboole_0(A_354, B_355)=B_355)), inference(resolution, [status(thm)], [c_3557, c_2])).
% 7.10/2.43  tff(c_4296, plain, (![A_382, B_383]: (r2_hidden('#skF_3'(A_382, B_383, B_383), B_383) | ~r1_tarski(A_382, B_383) | k2_xboole_0(A_382, B_383)=B_383)), inference(resolution, [status(thm)], [c_3821, c_22])).
% 7.10/2.43  tff(c_3919, plain, (![A_354, B_356]: (~r2_hidden('#skF_3'(A_354, B_356, B_356), B_356) | ~r1_tarski(A_354, B_356) | k2_xboole_0(A_354, B_356)=B_356)), inference(resolution, [status(thm)], [c_3821, c_14])).
% 7.10/2.43  tff(c_4361, plain, (![A_384, B_385]: (~r1_tarski(A_384, B_385) | k2_xboole_0(A_384, B_385)=B_385)), inference(resolution, [status(thm)], [c_4296, c_3919])).
% 7.10/2.43  tff(c_4386, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))=k2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_36, c_4361])).
% 7.10/2.43  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.43  tff(c_5133, plain, (![D_393]: (~r2_hidden(D_393, '#skF_5') | r2_hidden(D_393, k2_xboole_0('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_4386, c_12])).
% 7.10/2.43  tff(c_8, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.10/2.43  tff(c_5227, plain, (![D_394]: (r2_hidden(D_394, '#skF_7') | r2_hidden(D_394, '#skF_6') | ~r2_hidden(D_394, '#skF_5'))), inference(resolution, [status(thm)], [c_5133, c_8])).
% 7.10/2.43  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.10/2.43  tff(c_75, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, B_36) | ~r2_hidden(C_37, A_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.10/2.43  tff(c_78, plain, (![C_37]: (~r2_hidden(C_37, '#skF_7') | ~r2_hidden(C_37, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_75])).
% 7.10/2.43  tff(c_5352, plain, (![D_395]: (r2_hidden(D_395, '#skF_6') | ~r2_hidden(D_395, '#skF_5'))), inference(resolution, [status(thm)], [c_5227, c_78])).
% 7.10/2.43  tff(c_5486, plain, (![B_397]: (r2_hidden('#skF_1'('#skF_5', B_397), '#skF_6') | r1_tarski('#skF_5', B_397))), inference(resolution, [status(thm)], [c_6, c_5352])).
% 7.10/2.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.43  tff(c_5519, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_5486, c_4])).
% 7.10/2.43  tff(c_5535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_5519])).
% 7.10/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.43  
% 7.10/2.43  Inference rules
% 7.10/2.43  ----------------------
% 7.10/2.43  #Ref     : 0
% 7.10/2.43  #Sup     : 1392
% 7.10/2.43  #Fact    : 6
% 7.10/2.43  #Define  : 0
% 7.10/2.43  #Split   : 11
% 7.10/2.43  #Chain   : 0
% 7.10/2.43  #Close   : 0
% 7.10/2.43  
% 7.10/2.43  Ordering : KBO
% 7.10/2.43  
% 7.10/2.43  Simplification rules
% 7.10/2.43  ----------------------
% 7.10/2.43  #Subsume      : 391
% 7.10/2.43  #Demod        : 91
% 7.10/2.43  #Tautology    : 78
% 7.10/2.43  #SimpNegUnit  : 1
% 7.10/2.43  #BackRed      : 3
% 7.10/2.43  
% 7.10/2.43  #Partial instantiations: 0
% 7.10/2.43  #Strategies tried      : 1
% 7.10/2.43  
% 7.10/2.43  Timing (in seconds)
% 7.10/2.43  ----------------------
% 7.10/2.43  Preprocessing        : 0.28
% 7.10/2.43  Parsing              : 0.15
% 7.10/2.43  CNF conversion       : 0.02
% 7.10/2.43  Main loop            : 1.40
% 7.10/2.43  Inferencing          : 0.41
% 7.10/2.43  Reduction            : 0.28
% 7.10/2.43  Demodulation         : 0.19
% 7.10/2.43  BG Simplification    : 0.05
% 7.10/2.43  Subsumption          : 0.55
% 7.10/2.43  Abstraction          : 0.06
% 7.10/2.43  MUC search           : 0.00
% 7.10/2.43  Cooper               : 0.00
% 7.10/2.43  Total                : 1.70
% 7.10/2.43  Index Insertion      : 0.00
% 7.10/2.43  Index Deletion       : 0.00
% 7.10/2.43  Index Matching       : 0.00
% 7.10/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
