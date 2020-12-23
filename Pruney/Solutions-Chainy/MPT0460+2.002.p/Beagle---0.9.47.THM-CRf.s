%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:42 EST 2020

% Result     : Theorem 17.19s
% Output     : CNFRefutation 17.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 100 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 320 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( r1_tarski(A,B)
                 => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_38,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_122,B_123] :
      ( v1_relat_1(k5_relat_1(A_122,B_123))
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_6,B_16] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_16),'#skF_3'(A_6,B_16)),A_6)
      | r1_tarski(A_6,B_16)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [D_114,E_115,A_23,B_75] :
      ( r2_hidden(k4_tarski(D_114,'#skF_4'(D_114,E_115,k5_relat_1(A_23,B_75),B_75,A_23)),A_23)
      | ~ r2_hidden(k4_tarski(D_114,E_115),k5_relat_1(A_23,B_75))
      | ~ v1_relat_1(k5_relat_1(A_23,B_75))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    ! [D_176,E_177,A_178,B_179] :
      ( r2_hidden(k4_tarski('#skF_4'(D_176,E_177,k5_relat_1(A_178,B_179),B_179,A_178),E_177),B_179)
      | ~ r2_hidden(k4_tarski(D_176,E_177),k5_relat_1(A_178,B_179))
      | ~ v1_relat_1(k5_relat_1(A_178,B_179))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_236,plain,(
    ! [D_205,A_203,B_206,B_202,E_204] :
      ( r2_hidden(k4_tarski('#skF_4'(D_205,E_204,k5_relat_1(A_203,B_202),B_202,A_203),E_204),B_206)
      | ~ r1_tarski(B_202,B_206)
      | ~ r2_hidden(k4_tarski(D_205,E_204),k5_relat_1(A_203,B_202))
      | ~ v1_relat_1(k5_relat_1(A_203,B_202))
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_26,plain,(
    ! [E_115,B_75,F_118,A_23,D_114] :
      ( r2_hidden(k4_tarski(D_114,E_115),k5_relat_1(A_23,B_75))
      | ~ r2_hidden(k4_tarski(F_118,E_115),B_75)
      | ~ r2_hidden(k4_tarski(D_114,F_118),A_23)
      | ~ v1_relat_1(k5_relat_1(A_23,B_75))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6480,plain,(
    ! [A_1008,B_1006,D_1003,A_1002,E_1005,D_1004,B_1007] :
      ( r2_hidden(k4_tarski(D_1003,E_1005),k5_relat_1(A_1008,B_1006))
      | ~ r2_hidden(k4_tarski(D_1003,'#skF_4'(D_1004,E_1005,k5_relat_1(A_1002,B_1007),B_1007,A_1002)),A_1008)
      | ~ v1_relat_1(k5_relat_1(A_1008,B_1006))
      | ~ v1_relat_1(B_1006)
      | ~ v1_relat_1(A_1008)
      | ~ r1_tarski(B_1007,B_1006)
      | ~ r2_hidden(k4_tarski(D_1004,E_1005),k5_relat_1(A_1002,B_1007))
      | ~ v1_relat_1(k5_relat_1(A_1002,B_1007))
      | ~ v1_relat_1(B_1007)
      | ~ v1_relat_1(A_1002) ) ),
    inference(resolution,[status(thm)],[c_236,c_26])).

tff(c_6520,plain,(
    ! [B_1011,A_1013,B_1012,E_1010,D_1009] :
      ( r2_hidden(k4_tarski(D_1009,E_1010),k5_relat_1(A_1013,B_1011))
      | ~ v1_relat_1(k5_relat_1(A_1013,B_1011))
      | ~ v1_relat_1(B_1011)
      | ~ r1_tarski(B_1012,B_1011)
      | ~ r2_hidden(k4_tarski(D_1009,E_1010),k5_relat_1(A_1013,B_1012))
      | ~ v1_relat_1(k5_relat_1(A_1013,B_1012))
      | ~ v1_relat_1(B_1012)
      | ~ v1_relat_1(A_1013) ) ),
    inference(resolution,[status(thm)],[c_30,c_6480])).

tff(c_6534,plain,(
    ! [D_1009,E_1010,A_1013] :
      ( r2_hidden(k4_tarski(D_1009,E_1010),k5_relat_1(A_1013,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1013,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(k4_tarski(D_1009,E_1010),k5_relat_1(A_1013,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_1013,'#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1(A_1013) ) ),
    inference(resolution,[status(thm)],[c_36,c_6520])).

tff(c_6546,plain,(
    ! [D_1014,E_1015,A_1016] :
      ( r2_hidden(k4_tarski(D_1014,E_1015),k5_relat_1(A_1016,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1016,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_1014,E_1015),k5_relat_1(A_1016,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_1016,'#skF_10'))
      | ~ v1_relat_1(A_1016) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6534])).

tff(c_10,plain,(
    ! [A_6,B_16] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_6,B_16),'#skF_3'(A_6,B_16)),B_16)
      | r1_tarski(A_6,B_16)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15917,plain,(
    ! [A_1267,A_1268] :
      ( r1_tarski(A_1267,k5_relat_1(A_1268,'#skF_11'))
      | ~ v1_relat_1(A_1267)
      | ~ v1_relat_1(k5_relat_1(A_1268,'#skF_11'))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_1267,k5_relat_1(A_1268,'#skF_11')),'#skF_3'(A_1267,k5_relat_1(A_1268,'#skF_11'))),k5_relat_1(A_1268,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_1268,'#skF_10'))
      | ~ v1_relat_1(A_1268) ) ),
    inference(resolution,[status(thm)],[c_6546,c_10])).

tff(c_16054,plain,(
    ! [A_1269] :
      ( ~ v1_relat_1(k5_relat_1(A_1269,'#skF_11'))
      | ~ v1_relat_1(A_1269)
      | r1_tarski(k5_relat_1(A_1269,'#skF_10'),k5_relat_1(A_1269,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1269,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_12,c_15917])).

tff(c_34,plain,(
    ~ r1_tarski(k5_relat_1('#skF_12','#skF_10'),k5_relat_1('#skF_12','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16232,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_12','#skF_11'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1(k5_relat_1('#skF_12','#skF_10')) ),
    inference(resolution,[status(thm)],[c_16054,c_34])).

tff(c_16366,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_12','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_12','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16232])).

tff(c_16367,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_12','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_16366])).

tff(c_16370,plain,
    ( ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_32,c_16367])).

tff(c_16374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_16370])).

tff(c_16375,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_12','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_16366])).

tff(c_16379,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_32,c_16375])).

tff(c_16383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_16379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:47:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.19/8.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.19/8.06  
% 17.19/8.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.19/8.07  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12
% 17.19/8.07  
% 17.19/8.07  %Foreground sorts:
% 17.19/8.07  
% 17.19/8.07  
% 17.19/8.07  %Background operators:
% 17.19/8.07  
% 17.19/8.07  
% 17.19/8.07  %Foreground operators:
% 17.19/8.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.19/8.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.19/8.07  tff('#skF_11', type, '#skF_11': $i).
% 17.19/8.07  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.19/8.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.19/8.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 17.19/8.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 17.19/8.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.19/8.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.19/8.07  tff('#skF_10', type, '#skF_10': $i).
% 17.19/8.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.19/8.07  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 17.19/8.07  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 17.19/8.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.19/8.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.19/8.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.19/8.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.19/8.07  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 17.19/8.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.19/8.07  tff('#skF_12', type, '#skF_12': $i).
% 17.19/8.07  
% 17.19/8.08  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 17.19/8.08  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 17.19/8.08  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 17.19/8.08  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 17.19/8.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.19/8.08  tff(c_38, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.19/8.08  tff(c_40, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.19/8.08  tff(c_32, plain, (![A_122, B_123]: (v1_relat_1(k5_relat_1(A_122, B_123)) | ~v1_relat_1(B_123) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.19/8.08  tff(c_42, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.19/8.08  tff(c_12, plain, (![A_6, B_16]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_16), '#skF_3'(A_6, B_16)), A_6) | r1_tarski(A_6, B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.19/8.08  tff(c_36, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.19/8.08  tff(c_30, plain, (![D_114, E_115, A_23, B_75]: (r2_hidden(k4_tarski(D_114, '#skF_4'(D_114, E_115, k5_relat_1(A_23, B_75), B_75, A_23)), A_23) | ~r2_hidden(k4_tarski(D_114, E_115), k5_relat_1(A_23, B_75)) | ~v1_relat_1(k5_relat_1(A_23, B_75)) | ~v1_relat_1(B_75) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.19/8.08  tff(c_161, plain, (![D_176, E_177, A_178, B_179]: (r2_hidden(k4_tarski('#skF_4'(D_176, E_177, k5_relat_1(A_178, B_179), B_179, A_178), E_177), B_179) | ~r2_hidden(k4_tarski(D_176, E_177), k5_relat_1(A_178, B_179)) | ~v1_relat_1(k5_relat_1(A_178, B_179)) | ~v1_relat_1(B_179) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.19/8.08  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.19/8.08  tff(c_236, plain, (![D_205, A_203, B_206, B_202, E_204]: (r2_hidden(k4_tarski('#skF_4'(D_205, E_204, k5_relat_1(A_203, B_202), B_202, A_203), E_204), B_206) | ~r1_tarski(B_202, B_206) | ~r2_hidden(k4_tarski(D_205, E_204), k5_relat_1(A_203, B_202)) | ~v1_relat_1(k5_relat_1(A_203, B_202)) | ~v1_relat_1(B_202) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_161, c_2])).
% 17.19/8.08  tff(c_26, plain, (![E_115, B_75, F_118, A_23, D_114]: (r2_hidden(k4_tarski(D_114, E_115), k5_relat_1(A_23, B_75)) | ~r2_hidden(k4_tarski(F_118, E_115), B_75) | ~r2_hidden(k4_tarski(D_114, F_118), A_23) | ~v1_relat_1(k5_relat_1(A_23, B_75)) | ~v1_relat_1(B_75) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.19/8.08  tff(c_6480, plain, (![A_1008, B_1006, D_1003, A_1002, E_1005, D_1004, B_1007]: (r2_hidden(k4_tarski(D_1003, E_1005), k5_relat_1(A_1008, B_1006)) | ~r2_hidden(k4_tarski(D_1003, '#skF_4'(D_1004, E_1005, k5_relat_1(A_1002, B_1007), B_1007, A_1002)), A_1008) | ~v1_relat_1(k5_relat_1(A_1008, B_1006)) | ~v1_relat_1(B_1006) | ~v1_relat_1(A_1008) | ~r1_tarski(B_1007, B_1006) | ~r2_hidden(k4_tarski(D_1004, E_1005), k5_relat_1(A_1002, B_1007)) | ~v1_relat_1(k5_relat_1(A_1002, B_1007)) | ~v1_relat_1(B_1007) | ~v1_relat_1(A_1002))), inference(resolution, [status(thm)], [c_236, c_26])).
% 17.19/8.08  tff(c_6520, plain, (![B_1011, A_1013, B_1012, E_1010, D_1009]: (r2_hidden(k4_tarski(D_1009, E_1010), k5_relat_1(A_1013, B_1011)) | ~v1_relat_1(k5_relat_1(A_1013, B_1011)) | ~v1_relat_1(B_1011) | ~r1_tarski(B_1012, B_1011) | ~r2_hidden(k4_tarski(D_1009, E_1010), k5_relat_1(A_1013, B_1012)) | ~v1_relat_1(k5_relat_1(A_1013, B_1012)) | ~v1_relat_1(B_1012) | ~v1_relat_1(A_1013))), inference(resolution, [status(thm)], [c_30, c_6480])).
% 17.19/8.08  tff(c_6534, plain, (![D_1009, E_1010, A_1013]: (r2_hidden(k4_tarski(D_1009, E_1010), k5_relat_1(A_1013, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1013, '#skF_11')) | ~v1_relat_1('#skF_11') | ~r2_hidden(k4_tarski(D_1009, E_1010), k5_relat_1(A_1013, '#skF_10')) | ~v1_relat_1(k5_relat_1(A_1013, '#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1(A_1013))), inference(resolution, [status(thm)], [c_36, c_6520])).
% 17.19/8.08  tff(c_6546, plain, (![D_1014, E_1015, A_1016]: (r2_hidden(k4_tarski(D_1014, E_1015), k5_relat_1(A_1016, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1016, '#skF_11')) | ~r2_hidden(k4_tarski(D_1014, E_1015), k5_relat_1(A_1016, '#skF_10')) | ~v1_relat_1(k5_relat_1(A_1016, '#skF_10')) | ~v1_relat_1(A_1016))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6534])).
% 17.19/8.08  tff(c_10, plain, (![A_6, B_16]: (~r2_hidden(k4_tarski('#skF_2'(A_6, B_16), '#skF_3'(A_6, B_16)), B_16) | r1_tarski(A_6, B_16) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.19/8.08  tff(c_15917, plain, (![A_1267, A_1268]: (r1_tarski(A_1267, k5_relat_1(A_1268, '#skF_11')) | ~v1_relat_1(A_1267) | ~v1_relat_1(k5_relat_1(A_1268, '#skF_11')) | ~r2_hidden(k4_tarski('#skF_2'(A_1267, k5_relat_1(A_1268, '#skF_11')), '#skF_3'(A_1267, k5_relat_1(A_1268, '#skF_11'))), k5_relat_1(A_1268, '#skF_10')) | ~v1_relat_1(k5_relat_1(A_1268, '#skF_10')) | ~v1_relat_1(A_1268))), inference(resolution, [status(thm)], [c_6546, c_10])).
% 17.19/8.08  tff(c_16054, plain, (![A_1269]: (~v1_relat_1(k5_relat_1(A_1269, '#skF_11')) | ~v1_relat_1(A_1269) | r1_tarski(k5_relat_1(A_1269, '#skF_10'), k5_relat_1(A_1269, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1269, '#skF_10')))), inference(resolution, [status(thm)], [c_12, c_15917])).
% 17.19/8.08  tff(c_34, plain, (~r1_tarski(k5_relat_1('#skF_12', '#skF_10'), k5_relat_1('#skF_12', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.19/8.08  tff(c_16232, plain, (~v1_relat_1(k5_relat_1('#skF_12', '#skF_11')) | ~v1_relat_1('#skF_12') | ~v1_relat_1(k5_relat_1('#skF_12', '#skF_10'))), inference(resolution, [status(thm)], [c_16054, c_34])).
% 17.19/8.08  tff(c_16366, plain, (~v1_relat_1(k5_relat_1('#skF_12', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_12', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_16232])).
% 17.19/8.08  tff(c_16367, plain, (~v1_relat_1(k5_relat_1('#skF_12', '#skF_10'))), inference(splitLeft, [status(thm)], [c_16366])).
% 17.19/8.08  tff(c_16370, plain, (~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_32, c_16367])).
% 17.19/8.08  tff(c_16374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_16370])).
% 17.19/8.08  tff(c_16375, plain, (~v1_relat_1(k5_relat_1('#skF_12', '#skF_11'))), inference(splitRight, [status(thm)], [c_16366])).
% 17.19/8.08  tff(c_16379, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_32, c_16375])).
% 17.19/8.08  tff(c_16383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_16379])).
% 17.19/8.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.19/8.08  
% 17.19/8.08  Inference rules
% 17.19/8.08  ----------------------
% 17.19/8.08  #Ref     : 0
% 17.19/8.08  #Sup     : 3833
% 17.19/8.08  #Fact    : 0
% 17.19/8.08  #Define  : 0
% 17.19/8.08  #Split   : 17
% 17.19/8.08  #Chain   : 0
% 17.19/8.08  #Close   : 0
% 17.19/8.08  
% 17.19/8.08  Ordering : KBO
% 17.19/8.08  
% 17.19/8.08  Simplification rules
% 17.19/8.08  ----------------------
% 17.19/8.08  #Subsume      : 772
% 17.19/8.08  #Demod        : 1530
% 17.19/8.08  #Tautology    : 37
% 17.19/8.08  #SimpNegUnit  : 58
% 17.19/8.08  #BackRed      : 40
% 17.19/8.08  
% 17.19/8.08  #Partial instantiations: 0
% 17.19/8.08  #Strategies tried      : 1
% 17.19/8.08  
% 17.19/8.08  Timing (in seconds)
% 17.19/8.08  ----------------------
% 17.19/8.08  Preprocessing        : 0.33
% 17.19/8.08  Parsing              : 0.17
% 17.19/8.08  CNF conversion       : 0.04
% 17.19/8.08  Main loop            : 6.97
% 17.19/8.08  Inferencing          : 1.17
% 17.19/8.08  Reduction            : 1.00
% 17.19/8.08  Demodulation         : 0.64
% 17.19/8.08  BG Simplification    : 0.13
% 17.19/8.08  Subsumption          : 4.38
% 17.19/8.08  Abstraction          : 0.19
% 17.19/8.08  MUC search           : 0.00
% 17.19/8.08  Cooper               : 0.00
% 17.19/8.08  Total                : 7.33
% 17.19/8.08  Index Insertion      : 0.00
% 17.19/8.08  Index Deletion       : 0.00
% 17.19/8.08  Index Matching       : 0.00
% 17.19/8.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
