%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   51 (  87 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 276 expanded)
%              Number of equality atoms :   11 (  36 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C))
            & ! [D] :
                ( r2_hidden(D,k1_wellord1(C,A))
               => ( r2_hidden(k4_tarski(D,B),C)
                  & D != B ) ) )
         => r2_hidden(k4_tarski(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    v2_wellord1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_77,plain,(
    ! [A_31] :
      ( v1_relat_2(A_31)
      | ~ v2_wellord1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,
    ( v1_relat_2('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_83,plain,(
    v1_relat_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_80])).

tff(c_54,plain,(
    r2_hidden('#skF_6',k3_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [B_17,A_14] :
      ( r2_hidden(k4_tarski(B_17,B_17),A_14)
      | ~ r2_hidden(B_17,k3_relat_1(A_14))
      | ~ v1_relat_2(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_13] :
      ( v6_relat_2(A_13)
      | ~ v2_wellord1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_7',k1_wellord1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    r2_hidden('#skF_7',k3_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_266,plain,(
    ! [C_72,B_73,A_74] :
      ( r2_hidden(k4_tarski(C_72,B_73),A_74)
      | r2_hidden(k4_tarski(B_73,C_72),A_74)
      | C_72 = B_73
      | ~ r2_hidden(C_72,k3_relat_1(A_74))
      | ~ r2_hidden(B_73,k3_relat_1(A_74))
      | ~ v6_relat_2(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [D_12,A_1,B_8] :
      ( r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ r2_hidden(k4_tarski(D_12,B_8),A_1)
      | D_12 = B_8
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_351,plain,(
    ! [C_78,A_79,B_80] :
      ( r2_hidden(C_78,k1_wellord1(A_79,B_80))
      | r2_hidden(k4_tarski(B_80,C_78),A_79)
      | C_78 = B_80
      | ~ r2_hidden(C_78,k3_relat_1(A_79))
      | ~ r2_hidden(B_80,k3_relat_1(A_79))
      | ~ v6_relat_2(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_266,c_2])).

tff(c_50,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_385,plain,
    ( r2_hidden('#skF_7',k1_wellord1('#skF_8','#skF_6'))
    | '#skF_7' = '#skF_6'
    | ~ r2_hidden('#skF_7',k3_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_8'))
    | ~ v6_relat_2('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_351,c_50])).

tff(c_397,plain,
    ( r2_hidden('#skF_7',k1_wellord1('#skF_8','#skF_6'))
    | '#skF_7' = '#skF_6'
    | ~ v6_relat_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_385])).

tff(c_398,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v6_relat_2('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_397])).

tff(c_404,plain,(
    ~ v6_relat_2('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_410,plain,
    ( ~ v2_wellord1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_404])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_410])).

tff(c_418,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_426,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_50])).

tff(c_441,plain,
    ( ~ r2_hidden('#skF_6',k3_relat_1('#skF_8'))
    | ~ v1_relat_2('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_426])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_83,c_54,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.40  %$ r2_hidden > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.58/1.40  
% 2.58/1.40  %Foreground sorts:
% 2.58/1.40  
% 2.58/1.40  
% 2.58/1.40  %Background operators:
% 2.58/1.40  
% 2.58/1.40  
% 2.58/1.40  %Foreground operators:
% 2.58/1.40  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.58/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.58/1.40  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.58/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.40  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.58/1.40  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.58/1.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.58/1.40  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.58/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.58/1.40  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.58/1.40  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.58/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.58/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.58/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.58/1.40  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.58/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.40  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.58/1.40  
% 2.58/1.41  tff(f_99, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & (![D]: (r2_hidden(D, k1_wellord1(C, A)) => (r2_hidden(k4_tarski(D, B), C) & ~(D = B))))) => r2_hidden(k4_tarski(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_wellord1)).
% 2.58/1.41  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 2.58/1.41  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 2.58/1.41  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 2.58/1.41  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.58/1.41  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.41  tff(c_56, plain, (v2_wellord1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.41  tff(c_77, plain, (![A_31]: (v1_relat_2(A_31) | ~v2_wellord1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.41  tff(c_80, plain, (v1_relat_2('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_77])).
% 2.58/1.41  tff(c_83, plain, (v1_relat_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_80])).
% 2.58/1.41  tff(c_54, plain, (r2_hidden('#skF_6', k3_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.41  tff(c_32, plain, (![B_17, A_14]: (r2_hidden(k4_tarski(B_17, B_17), A_14) | ~r2_hidden(B_17, k3_relat_1(A_14)) | ~v1_relat_2(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.41  tff(c_24, plain, (![A_13]: (v6_relat_2(A_13) | ~v2_wellord1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.41  tff(c_60, plain, (~r2_hidden('#skF_7', k1_wellord1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.41  tff(c_52, plain, (r2_hidden('#skF_7', k3_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.41  tff(c_266, plain, (![C_72, B_73, A_74]: (r2_hidden(k4_tarski(C_72, B_73), A_74) | r2_hidden(k4_tarski(B_73, C_72), A_74) | C_72=B_73 | ~r2_hidden(C_72, k3_relat_1(A_74)) | ~r2_hidden(B_73, k3_relat_1(A_74)) | ~v6_relat_2(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.58/1.41  tff(c_2, plain, (![D_12, A_1, B_8]: (r2_hidden(D_12, k1_wellord1(A_1, B_8)) | ~r2_hidden(k4_tarski(D_12, B_8), A_1) | D_12=B_8 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.41  tff(c_351, plain, (![C_78, A_79, B_80]: (r2_hidden(C_78, k1_wellord1(A_79, B_80)) | r2_hidden(k4_tarski(B_80, C_78), A_79) | C_78=B_80 | ~r2_hidden(C_78, k3_relat_1(A_79)) | ~r2_hidden(B_80, k3_relat_1(A_79)) | ~v6_relat_2(A_79) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_266, c_2])).
% 2.58/1.41  tff(c_50, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.41  tff(c_385, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_8', '#skF_6')) | '#skF_7'='#skF_6' | ~r2_hidden('#skF_7', k3_relat_1('#skF_8')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_8')) | ~v6_relat_2('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_351, c_50])).
% 2.58/1.41  tff(c_397, plain, (r2_hidden('#skF_7', k1_wellord1('#skF_8', '#skF_6')) | '#skF_7'='#skF_6' | ~v6_relat_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_385])).
% 2.58/1.41  tff(c_398, plain, ('#skF_7'='#skF_6' | ~v6_relat_2('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_60, c_397])).
% 2.58/1.41  tff(c_404, plain, (~v6_relat_2('#skF_8')), inference(splitLeft, [status(thm)], [c_398])).
% 2.58/1.41  tff(c_410, plain, (~v2_wellord1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_24, c_404])).
% 2.58/1.41  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_410])).
% 2.58/1.41  tff(c_418, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_398])).
% 2.58/1.41  tff(c_426, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_50])).
% 2.58/1.41  tff(c_441, plain, (~r2_hidden('#skF_6', k3_relat_1('#skF_8')) | ~v1_relat_2('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_426])).
% 2.58/1.41  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_83, c_54, c_441])).
% 2.58/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  Inference rules
% 2.58/1.41  ----------------------
% 2.58/1.41  #Ref     : 0
% 2.58/1.41  #Sup     : 61
% 2.58/1.41  #Fact    : 2
% 2.58/1.41  #Define  : 0
% 2.58/1.41  #Split   : 3
% 2.58/1.41  #Chain   : 0
% 2.58/1.41  #Close   : 0
% 2.58/1.41  
% 2.58/1.41  Ordering : KBO
% 2.58/1.41  
% 2.58/1.41  Simplification rules
% 2.58/1.41  ----------------------
% 2.58/1.41  #Subsume      : 6
% 2.58/1.41  #Demod        : 36
% 2.58/1.41  #Tautology    : 17
% 2.58/1.41  #SimpNegUnit  : 2
% 2.58/1.41  #BackRed      : 8
% 2.58/1.41  
% 2.58/1.41  #Partial instantiations: 0
% 2.58/1.41  #Strategies tried      : 1
% 2.58/1.41  
% 2.58/1.41  Timing (in seconds)
% 2.58/1.41  ----------------------
% 2.58/1.41  Preprocessing        : 0.31
% 2.58/1.41  Parsing              : 0.16
% 2.58/1.41  CNF conversion       : 0.03
% 2.58/1.41  Main loop            : 0.28
% 2.58/1.41  Inferencing          : 0.11
% 2.58/1.41  Reduction            : 0.07
% 2.58/1.41  Demodulation         : 0.05
% 2.58/1.41  BG Simplification    : 0.02
% 2.58/1.41  Subsumption          : 0.06
% 2.58/1.41  Abstraction          : 0.02
% 2.58/1.41  MUC search           : 0.00
% 2.58/1.41  Cooper               : 0.00
% 2.58/1.41  Total                : 0.62
% 2.58/1.41  Index Insertion      : 0.00
% 2.58/1.41  Index Deletion       : 0.00
% 2.58/1.41  Index Matching       : 0.00
% 2.58/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
