%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:10 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 134 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 388 expanded)
%              Number of equality atoms :    8 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(c_30,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    r2_hidden('#skF_2',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k7_relat_1(B_9,A_8),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [A_50,C_51] :
      ( r2_hidden(k4_tarski(A_50,k1_funct_1(C_51,A_50)),C_51)
      | ~ r2_hidden(A_50,k1_relat_1(C_51))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_164,plain,(
    ! [A_71,C_72,B_73] :
      ( r2_hidden(k4_tarski(A_71,k1_funct_1(C_72,A_71)),B_73)
      | ~ r1_tarski(C_72,B_73)
      | ~ r2_hidden(A_71,k1_relat_1(C_72))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_28,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(A_17,k1_relat_1(C_19))
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_225,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden(A_82,k1_relat_1(B_83))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ r1_tarski(C_84,B_83)
      | ~ r2_hidden(A_82,k1_relat_1(C_84))
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_164,c_28])).

tff(c_280,plain,(
    ! [A_105,B_106,A_107] :
      ( r2_hidden(A_105,k1_relat_1(B_106))
      | ~ v1_funct_1(B_106)
      | ~ r2_hidden(A_105,k1_relat_1(k7_relat_1(B_106,A_107)))
      | ~ v1_funct_1(k7_relat_1(B_106,A_107))
      | ~ v1_relat_1(k7_relat_1(B_106,A_107))
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_10,c_225])).

tff(c_311,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_280])).

tff(c_321,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_311])).

tff(c_327,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_330,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_327])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_330])).

tff(c_336,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( v1_funct_1(k7_relat_1(A_15,B_16))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_335,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_337,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_340,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_337])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_340])).

tff(c_346,plain,(
    v1_funct_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_246,plain,(
    ! [C_93,A_94,B_95] :
      ( k1_funct_1(C_93,A_94) = k1_funct_1(B_95,A_94)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ r1_tarski(C_93,B_95)
      | ~ r2_hidden(A_94,k1_relat_1(C_93))
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_164,c_26])).

tff(c_1159,plain,(
    ! [B_187,A_188,A_189] :
      ( k1_funct_1(k7_relat_1(B_187,A_188),A_189) = k1_funct_1(B_187,A_189)
      | ~ v1_funct_1(B_187)
      | ~ r2_hidden(A_189,k1_relat_1(k7_relat_1(B_187,A_188)))
      | ~ v1_funct_1(k7_relat_1(B_187,A_188))
      | ~ v1_relat_1(k7_relat_1(B_187,A_188))
      | ~ v1_relat_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_10,c_246])).

tff(c_1202,plain,
    ( k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1159])).

tff(c_1215,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') = k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_336,c_346,c_34,c_1202])).

tff(c_1217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.55  
% 3.55/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.55  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.55/1.55  
% 3.55/1.55  %Foreground sorts:
% 3.55/1.55  
% 3.55/1.55  
% 3.55/1.55  %Background operators:
% 3.55/1.55  
% 3.55/1.55  
% 3.55/1.55  %Foreground operators:
% 3.55/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.55/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.55/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.55/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.55  
% 3.55/1.56  tff(f_85, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 3.55/1.56  tff(f_36, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.55/1.56  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.55/1.56  tff(f_76, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.55/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.55/1.56  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.55/1.56  tff(c_30, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.56  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.56  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/1.56  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.56  tff(c_32, plain, (r2_hidden('#skF_2', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.56  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k7_relat_1(B_9, A_8), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.56  tff(c_99, plain, (![A_50, C_51]: (r2_hidden(k4_tarski(A_50, k1_funct_1(C_51, A_50)), C_51) | ~r2_hidden(A_50, k1_relat_1(C_51)) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.55/1.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.56  tff(c_164, plain, (![A_71, C_72, B_73]: (r2_hidden(k4_tarski(A_71, k1_funct_1(C_72, A_71)), B_73) | ~r1_tarski(C_72, B_73) | ~r2_hidden(A_71, k1_relat_1(C_72)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_99, c_2])).
% 3.55/1.56  tff(c_28, plain, (![A_17, C_19, B_18]: (r2_hidden(A_17, k1_relat_1(C_19)) | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.55/1.56  tff(c_225, plain, (![A_82, B_83, C_84]: (r2_hidden(A_82, k1_relat_1(B_83)) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~r1_tarski(C_84, B_83) | ~r2_hidden(A_82, k1_relat_1(C_84)) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_164, c_28])).
% 3.55/1.56  tff(c_280, plain, (![A_105, B_106, A_107]: (r2_hidden(A_105, k1_relat_1(B_106)) | ~v1_funct_1(B_106) | ~r2_hidden(A_105, k1_relat_1(k7_relat_1(B_106, A_107))) | ~v1_funct_1(k7_relat_1(B_106, A_107)) | ~v1_relat_1(k7_relat_1(B_106, A_107)) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_10, c_225])).
% 3.55/1.56  tff(c_311, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_280])).
% 3.55/1.56  tff(c_321, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_311])).
% 3.55/1.56  tff(c_327, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_321])).
% 3.55/1.56  tff(c_330, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_327])).
% 3.55/1.56  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_330])).
% 3.55/1.56  tff(c_336, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_321])).
% 3.55/1.56  tff(c_20, plain, (![A_15, B_16]: (v1_funct_1(k7_relat_1(A_15, B_16)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.55/1.56  tff(c_335, plain, (~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_321])).
% 3.55/1.56  tff(c_337, plain, (~v1_funct_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_335])).
% 3.55/1.56  tff(c_340, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_337])).
% 3.55/1.56  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_340])).
% 3.55/1.56  tff(c_346, plain, (v1_funct_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_335])).
% 3.55/1.56  tff(c_26, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.55/1.56  tff(c_246, plain, (![C_93, A_94, B_95]: (k1_funct_1(C_93, A_94)=k1_funct_1(B_95, A_94) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | ~r1_tarski(C_93, B_95) | ~r2_hidden(A_94, k1_relat_1(C_93)) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_164, c_26])).
% 3.55/1.56  tff(c_1159, plain, (![B_187, A_188, A_189]: (k1_funct_1(k7_relat_1(B_187, A_188), A_189)=k1_funct_1(B_187, A_189) | ~v1_funct_1(B_187) | ~r2_hidden(A_189, k1_relat_1(k7_relat_1(B_187, A_188))) | ~v1_funct_1(k7_relat_1(B_187, A_188)) | ~v1_relat_1(k7_relat_1(B_187, A_188)) | ~v1_relat_1(B_187))), inference(resolution, [status(thm)], [c_10, c_246])).
% 3.55/1.56  tff(c_1202, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1159])).
% 3.55/1.56  tff(c_1215, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_336, c_346, c_34, c_1202])).
% 3.55/1.56  tff(c_1217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1215])).
% 3.55/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  Inference rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Ref     : 0
% 3.55/1.56  #Sup     : 255
% 3.55/1.56  #Fact    : 0
% 3.55/1.56  #Define  : 0
% 3.55/1.56  #Split   : 5
% 3.55/1.56  #Chain   : 0
% 3.55/1.56  #Close   : 0
% 3.55/1.56  
% 3.55/1.56  Ordering : KBO
% 3.55/1.56  
% 3.55/1.56  Simplification rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Subsume      : 31
% 3.55/1.56  #Demod        : 61
% 3.55/1.56  #Tautology    : 99
% 3.55/1.56  #SimpNegUnit  : 1
% 3.55/1.56  #BackRed      : 0
% 3.55/1.56  
% 3.55/1.56  #Partial instantiations: 0
% 3.55/1.56  #Strategies tried      : 1
% 3.55/1.56  
% 3.55/1.56  Timing (in seconds)
% 3.55/1.56  ----------------------
% 3.55/1.56  Preprocessing        : 0.28
% 3.55/1.56  Parsing              : 0.15
% 3.55/1.56  CNF conversion       : 0.02
% 3.55/1.56  Main loop            : 0.53
% 3.55/1.57  Inferencing          : 0.20
% 3.55/1.57  Reduction            : 0.13
% 3.55/1.57  Demodulation         : 0.09
% 3.55/1.57  BG Simplification    : 0.03
% 3.55/1.57  Subsumption          : 0.14
% 3.55/1.57  Abstraction          : 0.02
% 3.55/1.57  MUC search           : 0.00
% 3.55/1.57  Cooper               : 0.00
% 3.55/1.57  Total                : 0.84
% 3.55/1.57  Index Insertion      : 0.00
% 3.55/1.57  Index Deletion       : 0.00
% 3.55/1.57  Index Matching       : 0.00
% 3.55/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
