%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:42 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   50 (  99 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 320 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( r1_tarski(A,B)
                 => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_53,axiom,(
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

tff(c_34,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k5_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_154,plain,(
    ! [D_165,B_166,A_167,E_168] :
      ( r2_hidden(k4_tarski(D_165,'#skF_3'(B_166,A_167,k5_relat_1(A_167,B_166),D_165,E_168)),A_167)
      | ~ r2_hidden(k4_tarski(D_165,E_168),k5_relat_1(A_167,B_166))
      | ~ v1_relat_1(k5_relat_1(A_167,B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_16,D_17,B_11,A_1] :
      ( r2_hidden(k4_tarski(C_16,D_17),B_11)
      | ~ r2_hidden(k4_tarski(C_16,D_17),A_1)
      | ~ r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [B_166,B_11,A_167,E_168,D_165] :
      ( r2_hidden(k4_tarski(D_165,'#skF_3'(B_166,A_167,k5_relat_1(A_167,B_166),D_165,E_168)),B_11)
      | ~ r1_tarski(A_167,B_11)
      | ~ r2_hidden(k4_tarski(D_165,E_168),k5_relat_1(A_167,B_166))
      | ~ v1_relat_1(k5_relat_1(A_167,B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_147,plain,(
    ! [B_161,A_162,D_163,E_164] :
      ( r2_hidden(k4_tarski('#skF_3'(B_161,A_162,k5_relat_1(A_162,B_161),D_163,E_164),E_164),B_161)
      | ~ r2_hidden(k4_tarski(D_163,E_164),k5_relat_1(A_162,B_161))
      | ~ v1_relat_1(k5_relat_1(A_162,B_161))
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [B_70,F_113,D_109,E_110,A_18] :
      ( r2_hidden(k4_tarski(D_109,E_110),k5_relat_1(A_18,B_70))
      | ~ r2_hidden(k4_tarski(F_113,E_110),B_70)
      | ~ r2_hidden(k4_tarski(D_109,F_113),A_18)
      | ~ v1_relat_1(k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_670,plain,(
    ! [E_368,D_366,A_367,A_365,B_364,D_369] :
      ( r2_hidden(k4_tarski(D_369,E_368),k5_relat_1(A_365,B_364))
      | ~ r2_hidden(k4_tarski(D_369,'#skF_3'(B_364,A_367,k5_relat_1(A_367,B_364),D_366,E_368)),A_365)
      | ~ v1_relat_1(k5_relat_1(A_365,B_364))
      | ~ v1_relat_1(A_365)
      | ~ r2_hidden(k4_tarski(D_366,E_368),k5_relat_1(A_367,B_364))
      | ~ v1_relat_1(k5_relat_1(A_367,B_364))
      | ~ v1_relat_1(B_364)
      | ~ v1_relat_1(A_367) ) ),
    inference(resolution,[status(thm)],[c_147,c_20])).

tff(c_841,plain,(
    ! [D_376,E_374,A_378,B_377,B_375] :
      ( r2_hidden(k4_tarski(D_376,E_374),k5_relat_1(B_377,B_375))
      | ~ v1_relat_1(k5_relat_1(B_377,B_375))
      | ~ v1_relat_1(B_377)
      | ~ r1_tarski(A_378,B_377)
      | ~ r2_hidden(k4_tarski(D_376,E_374),k5_relat_1(A_378,B_375))
      | ~ v1_relat_1(k5_relat_1(A_378,B_375))
      | ~ v1_relat_1(B_375)
      | ~ v1_relat_1(A_378) ) ),
    inference(resolution,[status(thm)],[c_160,c_670])).

tff(c_847,plain,(
    ! [D_376,E_374,B_375] :
      ( r2_hidden(k4_tarski(D_376,E_374),k5_relat_1('#skF_10',B_375))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_375))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(k4_tarski(D_376,E_374),k5_relat_1('#skF_9',B_375))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_375))
      | ~ v1_relat_1(B_375)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_841])).

tff(c_855,plain,(
    ! [D_379,E_380,B_381] :
      ( r2_hidden(k4_tarski(D_379,E_380),k5_relat_1('#skF_10',B_381))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_381))
      | ~ r2_hidden(k4_tarski(D_379,E_380),k5_relat_1('#skF_9',B_381))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_381))
      | ~ v1_relat_1(B_381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_847])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1118,plain,(
    ! [A_389,B_390] :
      ( r1_tarski(A_389,k5_relat_1('#skF_10',B_390))
      | ~ v1_relat_1(A_389)
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_390))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_389,k5_relat_1('#skF_10',B_390)),'#skF_2'(A_389,k5_relat_1('#skF_10',B_390))),k5_relat_1('#skF_9',B_390))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_390))
      | ~ v1_relat_1(B_390) ) ),
    inference(resolution,[status(thm)],[c_855,c_4])).

tff(c_1162,plain,(
    ! [B_391] :
      ( ~ v1_relat_1(k5_relat_1('#skF_10',B_391))
      | ~ v1_relat_1(B_391)
      | r1_tarski(k5_relat_1('#skF_9',B_391),k5_relat_1('#skF_10',B_391))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_391)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1118])).

tff(c_28,plain,(
    ~ r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1194,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(resolution,[status(thm)],[c_1162,c_28])).

tff(c_1219,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1194])).

tff(c_1220,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_1223,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_1220])).

tff(c_1227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1223])).

tff(c_1228,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_1232,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_1228])).

tff(c_1236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  
% 4.13/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 4.13/1.75  
% 4.13/1.75  %Foreground sorts:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Background operators:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Foreground operators:
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.75  tff('#skF_11', type, '#skF_11': $i).
% 4.13/1.75  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.13/1.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.13/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.13/1.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.13/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.75  tff('#skF_10', type, '#skF_10': $i).
% 4.13/1.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.13/1.75  tff('#skF_9', type, '#skF_9': $i).
% 4.13/1.75  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.13/1.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.13/1.75  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.13/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.13/1.75  
% 4.13/1.76  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relat_1)).
% 4.13/1.76  tff(f_59, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.13/1.76  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 4.13/1.76  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 4.13/1.76  tff(c_34, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.13/1.76  tff(c_32, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.13/1.76  tff(c_26, plain, (![A_117, B_118]: (v1_relat_1(k5_relat_1(A_117, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.13/1.76  tff(c_36, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.13/1.76  tff(c_6, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.76  tff(c_30, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.13/1.76  tff(c_154, plain, (![D_165, B_166, A_167, E_168]: (r2_hidden(k4_tarski(D_165, '#skF_3'(B_166, A_167, k5_relat_1(A_167, B_166), D_165, E_168)), A_167) | ~r2_hidden(k4_tarski(D_165, E_168), k5_relat_1(A_167, B_166)) | ~v1_relat_1(k5_relat_1(A_167, B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.13/1.76  tff(c_2, plain, (![C_16, D_17, B_11, A_1]: (r2_hidden(k4_tarski(C_16, D_17), B_11) | ~r2_hidden(k4_tarski(C_16, D_17), A_1) | ~r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.76  tff(c_160, plain, (![B_166, B_11, A_167, E_168, D_165]: (r2_hidden(k4_tarski(D_165, '#skF_3'(B_166, A_167, k5_relat_1(A_167, B_166), D_165, E_168)), B_11) | ~r1_tarski(A_167, B_11) | ~r2_hidden(k4_tarski(D_165, E_168), k5_relat_1(A_167, B_166)) | ~v1_relat_1(k5_relat_1(A_167, B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_154, c_2])).
% 4.13/1.76  tff(c_147, plain, (![B_161, A_162, D_163, E_164]: (r2_hidden(k4_tarski('#skF_3'(B_161, A_162, k5_relat_1(A_162, B_161), D_163, E_164), E_164), B_161) | ~r2_hidden(k4_tarski(D_163, E_164), k5_relat_1(A_162, B_161)) | ~v1_relat_1(k5_relat_1(A_162, B_161)) | ~v1_relat_1(B_161) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.13/1.76  tff(c_20, plain, (![B_70, F_113, D_109, E_110, A_18]: (r2_hidden(k4_tarski(D_109, E_110), k5_relat_1(A_18, B_70)) | ~r2_hidden(k4_tarski(F_113, E_110), B_70) | ~r2_hidden(k4_tarski(D_109, F_113), A_18) | ~v1_relat_1(k5_relat_1(A_18, B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.13/1.76  tff(c_670, plain, (![E_368, D_366, A_367, A_365, B_364, D_369]: (r2_hidden(k4_tarski(D_369, E_368), k5_relat_1(A_365, B_364)) | ~r2_hidden(k4_tarski(D_369, '#skF_3'(B_364, A_367, k5_relat_1(A_367, B_364), D_366, E_368)), A_365) | ~v1_relat_1(k5_relat_1(A_365, B_364)) | ~v1_relat_1(A_365) | ~r2_hidden(k4_tarski(D_366, E_368), k5_relat_1(A_367, B_364)) | ~v1_relat_1(k5_relat_1(A_367, B_364)) | ~v1_relat_1(B_364) | ~v1_relat_1(A_367))), inference(resolution, [status(thm)], [c_147, c_20])).
% 4.13/1.76  tff(c_841, plain, (![D_376, E_374, A_378, B_377, B_375]: (r2_hidden(k4_tarski(D_376, E_374), k5_relat_1(B_377, B_375)) | ~v1_relat_1(k5_relat_1(B_377, B_375)) | ~v1_relat_1(B_377) | ~r1_tarski(A_378, B_377) | ~r2_hidden(k4_tarski(D_376, E_374), k5_relat_1(A_378, B_375)) | ~v1_relat_1(k5_relat_1(A_378, B_375)) | ~v1_relat_1(B_375) | ~v1_relat_1(A_378))), inference(resolution, [status(thm)], [c_160, c_670])).
% 4.13/1.76  tff(c_847, plain, (![D_376, E_374, B_375]: (r2_hidden(k4_tarski(D_376, E_374), k5_relat_1('#skF_10', B_375)) | ~v1_relat_1(k5_relat_1('#skF_10', B_375)) | ~v1_relat_1('#skF_10') | ~r2_hidden(k4_tarski(D_376, E_374), k5_relat_1('#skF_9', B_375)) | ~v1_relat_1(k5_relat_1('#skF_9', B_375)) | ~v1_relat_1(B_375) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_841])).
% 4.13/1.76  tff(c_855, plain, (![D_379, E_380, B_381]: (r2_hidden(k4_tarski(D_379, E_380), k5_relat_1('#skF_10', B_381)) | ~v1_relat_1(k5_relat_1('#skF_10', B_381)) | ~r2_hidden(k4_tarski(D_379, E_380), k5_relat_1('#skF_9', B_381)) | ~v1_relat_1(k5_relat_1('#skF_9', B_381)) | ~v1_relat_1(B_381))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_847])).
% 4.13/1.76  tff(c_4, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.76  tff(c_1118, plain, (![A_389, B_390]: (r1_tarski(A_389, k5_relat_1('#skF_10', B_390)) | ~v1_relat_1(A_389) | ~v1_relat_1(k5_relat_1('#skF_10', B_390)) | ~r2_hidden(k4_tarski('#skF_1'(A_389, k5_relat_1('#skF_10', B_390)), '#skF_2'(A_389, k5_relat_1('#skF_10', B_390))), k5_relat_1('#skF_9', B_390)) | ~v1_relat_1(k5_relat_1('#skF_9', B_390)) | ~v1_relat_1(B_390))), inference(resolution, [status(thm)], [c_855, c_4])).
% 4.13/1.76  tff(c_1162, plain, (![B_391]: (~v1_relat_1(k5_relat_1('#skF_10', B_391)) | ~v1_relat_1(B_391) | r1_tarski(k5_relat_1('#skF_9', B_391), k5_relat_1('#skF_10', B_391)) | ~v1_relat_1(k5_relat_1('#skF_9', B_391)))), inference(resolution, [status(thm)], [c_6, c_1118])).
% 4.13/1.76  tff(c_28, plain, (~r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.13/1.76  tff(c_1194, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(resolution, [status(thm)], [c_1162, c_28])).
% 4.13/1.76  tff(c_1219, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1194])).
% 4.13/1.76  tff(c_1220, plain, (~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_1219])).
% 4.13/1.76  tff(c_1223, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_1220])).
% 4.13/1.76  tff(c_1227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1223])).
% 4.13/1.76  tff(c_1228, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_1219])).
% 4.13/1.76  tff(c_1232, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_26, c_1228])).
% 4.13/1.76  tff(c_1236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1232])).
% 4.13/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.76  
% 4.13/1.76  Inference rules
% 4.13/1.76  ----------------------
% 4.13/1.76  #Ref     : 0
% 4.13/1.76  #Sup     : 272
% 4.13/1.76  #Fact    : 0
% 4.13/1.76  #Define  : 0
% 4.13/1.76  #Split   : 2
% 4.13/1.76  #Chain   : 0
% 4.13/1.76  #Close   : 0
% 4.13/1.76  
% 4.13/1.76  Ordering : KBO
% 4.13/1.76  
% 4.13/1.76  Simplification rules
% 4.13/1.76  ----------------------
% 4.13/1.76  #Subsume      : 37
% 4.13/1.76  #Demod        : 57
% 4.13/1.76  #Tautology    : 3
% 4.13/1.76  #SimpNegUnit  : 0
% 4.13/1.76  #BackRed      : 0
% 4.13/1.76  
% 4.13/1.76  #Partial instantiations: 0
% 4.13/1.76  #Strategies tried      : 1
% 4.13/1.76  
% 4.13/1.76  Timing (in seconds)
% 4.13/1.76  ----------------------
% 4.13/1.77  Preprocessing        : 0.29
% 4.13/1.77  Parsing              : 0.15
% 4.13/1.77  CNF conversion       : 0.04
% 4.13/1.77  Main loop            : 0.69
% 4.13/1.77  Inferencing          : 0.23
% 4.13/1.77  Reduction            : 0.14
% 4.13/1.77  Demodulation         : 0.09
% 4.13/1.77  BG Simplification    : 0.03
% 4.13/1.77  Subsumption          : 0.25
% 4.13/1.77  Abstraction          : 0.03
% 4.13/1.77  MUC search           : 0.00
% 4.13/1.77  Cooper               : 0.00
% 4.13/1.77  Total                : 1.00
% 4.13/1.77  Index Insertion      : 0.00
% 4.13/1.77  Index Deletion       : 0.00
% 4.13/1.77  Index Matching       : 0.00
% 4.13/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
