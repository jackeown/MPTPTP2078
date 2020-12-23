%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:41 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  84 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_3 > #skF_13 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_21,A_6] :
      ( r2_hidden(k4_tarski(C_21,'#skF_5'(A_6,k1_relat_1(A_6),C_21)),A_6)
      | ~ r2_hidden(C_21,k1_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_233,plain,(
    ! [D_198,B_199,A_200,E_201] :
      ( r2_hidden(k4_tarski(D_198,'#skF_6'(D_198,B_199,A_200,E_201,k5_relat_1(A_200,B_199))),A_200)
      | ~ r2_hidden(k4_tarski(D_198,E_201),k5_relat_1(A_200,B_199))
      | ~ v1_relat_1(k5_relat_1(A_200,B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_248,plain,(
    ! [D_202,A_203,E_204,B_205] :
      ( r2_hidden(D_202,k1_relat_1(A_203))
      | ~ r2_hidden(k4_tarski(D_202,E_204),k5_relat_1(A_203,B_205))
      | ~ v1_relat_1(k5_relat_1(A_203,B_205))
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_274,plain,(
    ! [C_206,A_207,B_208] :
      ( r2_hidden(C_206,k1_relat_1(A_207))
      | ~ v1_relat_1(k5_relat_1(A_207,B_208))
      | ~ v1_relat_1(B_208)
      | ~ v1_relat_1(A_207)
      | ~ r2_hidden(C_206,k1_relat_1(k5_relat_1(A_207,B_208))) ) ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_1031,plain,(
    ! [A_316,B_317,B_318] :
      ( r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(A_316,B_317)),B_318),k1_relat_1(A_316))
      | ~ v1_relat_1(k5_relat_1(A_316,B_317))
      | ~ v1_relat_1(B_317)
      | ~ v1_relat_1(A_316)
      | r1_tarski(k1_relat_1(k5_relat_1(A_316,B_317)),B_318) ) ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1045,plain,(
    ! [A_319,B_320] :
      ( ~ v1_relat_1(k5_relat_1(A_319,B_320))
      | ~ v1_relat_1(B_320)
      | ~ v1_relat_1(A_319)
      | r1_tarski(k1_relat_1(k5_relat_1(A_319,B_320)),k1_relat_1(A_319)) ) ),
    inference(resolution,[status(thm)],[c_1031,c_4])).

tff(c_40,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_12','#skF_13')),k1_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1071,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
    | ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1045,c_40])).

tff(c_1085,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1071])).

tff(c_1097,plain,
    ( ~ v1_relat_1('#skF_13')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_38,c_1085])).

tff(c_1101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1097])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.53  
% 3.45/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.54  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_3 > #skF_13 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10
% 3.45/1.54  
% 3.45/1.54  %Foreground sorts:
% 3.45/1.54  
% 3.45/1.54  
% 3.45/1.54  %Background operators:
% 3.45/1.54  
% 3.45/1.54  
% 3.45/1.54  %Foreground operators:
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.45/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.45/1.54  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.45/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.54  tff('#skF_13', type, '#skF_13': $i).
% 3.45/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.45/1.54  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.45/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.45/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.54  tff('#skF_12', type, '#skF_12': $i).
% 3.45/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.45/1.54  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.45/1.54  
% 3.45/1.54  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 3.45/1.54  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.45/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.45/1.54  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.45/1.54  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.45/1.54  tff(c_44, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.54  tff(c_42, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.54  tff(c_38, plain, (![A_124, B_125]: (v1_relat_1(k5_relat_1(A_124, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.54  tff(c_8, plain, (![C_21, A_6]: (r2_hidden(k4_tarski(C_21, '#skF_5'(A_6, k1_relat_1(A_6), C_21)), A_6) | ~r2_hidden(C_21, k1_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.45/1.54  tff(c_233, plain, (![D_198, B_199, A_200, E_201]: (r2_hidden(k4_tarski(D_198, '#skF_6'(D_198, B_199, A_200, E_201, k5_relat_1(A_200, B_199))), A_200) | ~r2_hidden(k4_tarski(D_198, E_201), k5_relat_1(A_200, B_199)) | ~v1_relat_1(k5_relat_1(A_200, B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.54  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.45/1.54  tff(c_248, plain, (![D_202, A_203, E_204, B_205]: (r2_hidden(D_202, k1_relat_1(A_203)) | ~r2_hidden(k4_tarski(D_202, E_204), k5_relat_1(A_203, B_205)) | ~v1_relat_1(k5_relat_1(A_203, B_205)) | ~v1_relat_1(B_205) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_233, c_10])).
% 3.45/1.54  tff(c_274, plain, (![C_206, A_207, B_208]: (r2_hidden(C_206, k1_relat_1(A_207)) | ~v1_relat_1(k5_relat_1(A_207, B_208)) | ~v1_relat_1(B_208) | ~v1_relat_1(A_207) | ~r2_hidden(C_206, k1_relat_1(k5_relat_1(A_207, B_208))))), inference(resolution, [status(thm)], [c_8, c_248])).
% 3.45/1.54  tff(c_1031, plain, (![A_316, B_317, B_318]: (r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(A_316, B_317)), B_318), k1_relat_1(A_316)) | ~v1_relat_1(k5_relat_1(A_316, B_317)) | ~v1_relat_1(B_317) | ~v1_relat_1(A_316) | r1_tarski(k1_relat_1(k5_relat_1(A_316, B_317)), B_318))), inference(resolution, [status(thm)], [c_6, c_274])).
% 3.45/1.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.45/1.54  tff(c_1045, plain, (![A_319, B_320]: (~v1_relat_1(k5_relat_1(A_319, B_320)) | ~v1_relat_1(B_320) | ~v1_relat_1(A_319) | r1_tarski(k1_relat_1(k5_relat_1(A_319, B_320)), k1_relat_1(A_319)))), inference(resolution, [status(thm)], [c_1031, c_4])).
% 3.45/1.54  tff(c_40, plain, (~r1_tarski(k1_relat_1(k5_relat_1('#skF_12', '#skF_13')), k1_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.54  tff(c_1071, plain, (~v1_relat_1(k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_1045, c_40])).
% 3.45/1.54  tff(c_1085, plain, (~v1_relat_1(k5_relat_1('#skF_12', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1071])).
% 3.45/1.54  tff(c_1097, plain, (~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_38, c_1085])).
% 3.45/1.54  tff(c_1101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1097])).
% 3.45/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.54  
% 3.45/1.54  Inference rules
% 3.45/1.54  ----------------------
% 3.45/1.54  #Ref     : 0
% 3.45/1.54  #Sup     : 224
% 3.45/1.54  #Fact    : 0
% 3.45/1.54  #Define  : 0
% 3.45/1.54  #Split   : 0
% 3.45/1.54  #Chain   : 0
% 3.45/1.54  #Close   : 0
% 3.45/1.54  
% 3.45/1.54  Ordering : KBO
% 3.45/1.54  
% 3.45/1.54  Simplification rules
% 3.45/1.54  ----------------------
% 3.45/1.54  #Subsume      : 38
% 3.45/1.54  #Demod        : 25
% 3.45/1.54  #Tautology    : 28
% 3.45/1.54  #SimpNegUnit  : 0
% 3.45/1.54  #BackRed      : 0
% 3.45/1.54  
% 3.45/1.54  #Partial instantiations: 0
% 3.45/1.54  #Strategies tried      : 1
% 3.45/1.54  
% 3.45/1.54  Timing (in seconds)
% 3.45/1.54  ----------------------
% 3.45/1.55  Preprocessing        : 0.29
% 3.45/1.55  Parsing              : 0.15
% 3.45/1.55  CNF conversion       : 0.04
% 3.45/1.55  Main loop            : 0.48
% 3.45/1.55  Inferencing          : 0.20
% 3.45/1.55  Reduction            : 0.10
% 3.45/1.55  Demodulation         : 0.07
% 3.45/1.55  BG Simplification    : 0.03
% 3.45/1.55  Subsumption          : 0.13
% 3.45/1.55  Abstraction          : 0.03
% 3.45/1.55  MUC search           : 0.00
% 3.45/1.55  Cooper               : 0.00
% 3.45/1.55  Total                : 0.80
% 3.45/1.55  Index Insertion      : 0.00
% 3.45/1.55  Index Deletion       : 0.00
% 3.45/1.55  Index Matching       : 0.00
% 3.45/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
