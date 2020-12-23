%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 106 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 272 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( ( r1_tarski(k1_relat_1(C),A)
                & r1_tarski(C,B) )
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_9',k7_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_44] :
      ( k7_relat_1(A_44,k1_relat_1(A_44)) = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,(
    ! [B_49,A_50] :
      ( k7_relat_1(B_49,A_50) = B_49
      | ~ r1_tarski(k1_relat_1(B_49),A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,
    ( k7_relat_1('#skF_9','#skF_7') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_62,plain,(
    k7_relat_1('#skF_9','#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59])).

tff(c_72,plain,(
    ! [C_51,A_52,B_53] :
      ( r1_tarski(k7_relat_1(C_51,A_52),k7_relat_1(C_51,B_53))
      | ~ r1_tarski(A_52,B_53)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    ! [A_52] :
      ( r1_tarski(k7_relat_1('#skF_9',A_52),'#skF_9')
      | ~ r1_tarski(A_52,'#skF_7')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_72])).

tff(c_102,plain,(
    ! [A_57] :
      ( r1_tarski(k7_relat_1('#skF_9',A_57),'#skF_9')
      | ~ r1_tarski(A_57,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_78])).

tff(c_109,plain,
    ( r1_tarski('#skF_9','#skF_9')
    | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_111,plain,(
    r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_109])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [D_70,B_71,E_72,A_73] :
      ( r2_hidden(D_70,B_71)
      | ~ r2_hidden(k4_tarski(D_70,E_72),k7_relat_1(A_73,B_71))
      | ~ v1_relat_1(k7_relat_1(A_73,B_71))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [D_70,E_72] :
      ( r2_hidden(D_70,'#skF_7')
      | ~ r2_hidden(k4_tarski(D_70,E_72),'#skF_9')
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_164])).

tff(c_178,plain,(
    ! [D_74,E_75] :
      ( r2_hidden(D_74,'#skF_7')
      | ~ r2_hidden(k4_tarski(D_74,E_75),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_62,c_171])).

tff(c_182,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_5'('#skF_9',B_30),'#skF_7')
      | r1_tarski('#skF_9',B_30)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_178])).

tff(c_185,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_5'('#skF_9',B_30),'#skF_7')
      | r1_tarski('#skF_9',B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_182])).

tff(c_36,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_160,plain,(
    ! [C_66,D_67,B_68,A_69] :
      ( r2_hidden(k4_tarski(C_66,D_67),B_68)
      | ~ r2_hidden(k4_tarski(C_66,D_67),A_69)
      | ~ r1_tarski(A_69,B_68)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_201,plain,(
    ! [A_81,B_82,B_83] :
      ( r2_hidden(k4_tarski('#skF_5'(A_81,B_82),'#skF_6'(A_81,B_82)),B_83)
      | ~ r1_tarski(A_81,B_83)
      | r1_tarski(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_20,plain,(
    ! [C_35,D_36,B_30,A_20] :
      ( r2_hidden(k4_tarski(C_35,D_36),B_30)
      | ~ r2_hidden(k4_tarski(C_35,D_36),A_20)
      | ~ r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_376,plain,(
    ! [A_114,B_115,B_116,B_117] :
      ( r2_hidden(k4_tarski('#skF_5'(A_114,B_115),'#skF_6'(A_114,B_115)),B_116)
      | ~ r1_tarski(B_117,B_116)
      | ~ v1_relat_1(B_117)
      | ~ r1_tarski(A_114,B_117)
      | r1_tarski(A_114,B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_201,c_20])).

tff(c_396,plain,(
    ! [A_114,B_115] :
      ( r2_hidden(k4_tarski('#skF_5'(A_114,B_115),'#skF_6'(A_114,B_115)),'#skF_8')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_114,'#skF_9')
      | r1_tarski(A_114,B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_36,c_376])).

tff(c_412,plain,(
    ! [A_114,B_115] :
      ( r2_hidden(k4_tarski('#skF_5'(A_114,B_115),'#skF_6'(A_114,B_115)),'#skF_8')
      | ~ r1_tarski(A_114,'#skF_9')
      | r1_tarski(A_114,B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_396])).

tff(c_243,plain,(
    ! [D_94,E_95,A_96,B_97] :
      ( r2_hidden(k4_tarski(D_94,E_95),k7_relat_1(A_96,B_97))
      | ~ r2_hidden(k4_tarski(D_94,E_95),A_96)
      | ~ r2_hidden(D_94,B_97)
      | ~ v1_relat_1(k7_relat_1(A_96,B_97))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3051,plain,(
    ! [A_266,A_267,B_268] :
      ( r1_tarski(A_266,k7_relat_1(A_267,B_268))
      | ~ v1_relat_1(A_266)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_266,k7_relat_1(A_267,B_268)),'#skF_6'(A_266,k7_relat_1(A_267,B_268))),A_267)
      | ~ r2_hidden('#skF_5'(A_266,k7_relat_1(A_267,B_268)),B_268)
      | ~ v1_relat_1(k7_relat_1(A_267,B_268))
      | ~ v1_relat_1(A_267) ) ),
    inference(resolution,[status(thm)],[c_243,c_22])).

tff(c_3107,plain,(
    ! [A_114,B_268] :
      ( ~ r2_hidden('#skF_5'(A_114,k7_relat_1('#skF_8',B_268)),B_268)
      | ~ v1_relat_1(k7_relat_1('#skF_8',B_268))
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(A_114,'#skF_9')
      | r1_tarski(A_114,k7_relat_1('#skF_8',B_268))
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_412,c_3051])).

tff(c_3269,plain,(
    ! [A_273,B_274] :
      ( ~ r2_hidden('#skF_5'(A_273,k7_relat_1('#skF_8',B_274)),B_274)
      | ~ v1_relat_1(k7_relat_1('#skF_8',B_274))
      | ~ r1_tarski(A_273,'#skF_9')
      | r1_tarski(A_273,k7_relat_1('#skF_8',B_274))
      | ~ v1_relat_1(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3107])).

tff(c_3337,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7'))
    | ~ r1_tarski('#skF_9','#skF_9')
    | ~ v1_relat_1('#skF_9')
    | r1_tarski('#skF_9',k7_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_185,c_3269])).

tff(c_3371,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7'))
    | r1_tarski('#skF_9',k7_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_111,c_3337])).

tff(c_3372,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3371])).

tff(c_3377,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_3372])).

tff(c_3381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.98  
% 5.06/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.98  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 5.06/1.98  
% 5.06/1.98  %Foreground sorts:
% 5.06/1.98  
% 5.06/1.98  
% 5.06/1.98  %Background operators:
% 5.06/1.98  
% 5.06/1.98  
% 5.06/1.98  %Foreground operators:
% 5.06/1.98  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.06/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.06/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/1.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.06/1.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.06/1.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.06/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.06/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.06/1.98  tff('#skF_9', type, '#skF_9': $i).
% 5.06/1.98  tff('#skF_8', type, '#skF_8': $i).
% 5.06/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/1.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.06/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.06/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/1.98  
% 5.40/2.00  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 5.40/2.00  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.40/2.00  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 5.40/2.00  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.40/2.00  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 5.40/2.00  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 5.40/2.00  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 5.40/2.00  tff(c_42, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.40/2.00  tff(c_26, plain, (![A_37, B_38]: (v1_relat_1(k7_relat_1(A_37, B_38)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.40/2.00  tff(c_34, plain, (~r1_tarski('#skF_9', k7_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.40/2.00  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.40/2.00  tff(c_38, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.40/2.00  tff(c_32, plain, (![A_44]: (k7_relat_1(A_44, k1_relat_1(A_44))=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.40/2.00  tff(c_56, plain, (![B_49, A_50]: (k7_relat_1(B_49, A_50)=B_49 | ~r1_tarski(k1_relat_1(B_49), A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.40/2.00  tff(c_59, plain, (k7_relat_1('#skF_9', '#skF_7')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_56])).
% 5.40/2.00  tff(c_62, plain, (k7_relat_1('#skF_9', '#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59])).
% 5.40/2.00  tff(c_72, plain, (![C_51, A_52, B_53]: (r1_tarski(k7_relat_1(C_51, A_52), k7_relat_1(C_51, B_53)) | ~r1_tarski(A_52, B_53) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.40/2.00  tff(c_78, plain, (![A_52]: (r1_tarski(k7_relat_1('#skF_9', A_52), '#skF_9') | ~r1_tarski(A_52, '#skF_7') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_72])).
% 5.40/2.00  tff(c_102, plain, (![A_57]: (r1_tarski(k7_relat_1('#skF_9', A_57), '#skF_9') | ~r1_tarski(A_57, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_78])).
% 5.40/2.00  tff(c_109, plain, (r1_tarski('#skF_9', '#skF_9') | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_32, c_102])).
% 5.40/2.00  tff(c_111, plain, (r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_109])).
% 5.40/2.00  tff(c_24, plain, (![A_20, B_30]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_20) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.40/2.00  tff(c_164, plain, (![D_70, B_71, E_72, A_73]: (r2_hidden(D_70, B_71) | ~r2_hidden(k4_tarski(D_70, E_72), k7_relat_1(A_73, B_71)) | ~v1_relat_1(k7_relat_1(A_73, B_71)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.40/2.00  tff(c_171, plain, (![D_70, E_72]: (r2_hidden(D_70, '#skF_7') | ~r2_hidden(k4_tarski(D_70, E_72), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_164])).
% 5.40/2.00  tff(c_178, plain, (![D_74, E_75]: (r2_hidden(D_74, '#skF_7') | ~r2_hidden(k4_tarski(D_74, E_75), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_62, c_171])).
% 5.40/2.00  tff(c_182, plain, (![B_30]: (r2_hidden('#skF_5'('#skF_9', B_30), '#skF_7') | r1_tarski('#skF_9', B_30) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_178])).
% 5.40/2.00  tff(c_185, plain, (![B_30]: (r2_hidden('#skF_5'('#skF_9', B_30), '#skF_7') | r1_tarski('#skF_9', B_30))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_182])).
% 5.40/2.00  tff(c_36, plain, (r1_tarski('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.40/2.00  tff(c_160, plain, (![C_66, D_67, B_68, A_69]: (r2_hidden(k4_tarski(C_66, D_67), B_68) | ~r2_hidden(k4_tarski(C_66, D_67), A_69) | ~r1_tarski(A_69, B_68) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.40/2.00  tff(c_201, plain, (![A_81, B_82, B_83]: (r2_hidden(k4_tarski('#skF_5'(A_81, B_82), '#skF_6'(A_81, B_82)), B_83) | ~r1_tarski(A_81, B_83) | r1_tarski(A_81, B_82) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_24, c_160])).
% 5.40/2.00  tff(c_20, plain, (![C_35, D_36, B_30, A_20]: (r2_hidden(k4_tarski(C_35, D_36), B_30) | ~r2_hidden(k4_tarski(C_35, D_36), A_20) | ~r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.40/2.00  tff(c_376, plain, (![A_114, B_115, B_116, B_117]: (r2_hidden(k4_tarski('#skF_5'(A_114, B_115), '#skF_6'(A_114, B_115)), B_116) | ~r1_tarski(B_117, B_116) | ~v1_relat_1(B_117) | ~r1_tarski(A_114, B_117) | r1_tarski(A_114, B_115) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_201, c_20])).
% 5.40/2.00  tff(c_396, plain, (![A_114, B_115]: (r2_hidden(k4_tarski('#skF_5'(A_114, B_115), '#skF_6'(A_114, B_115)), '#skF_8') | ~v1_relat_1('#skF_9') | ~r1_tarski(A_114, '#skF_9') | r1_tarski(A_114, B_115) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_36, c_376])).
% 5.40/2.00  tff(c_412, plain, (![A_114, B_115]: (r2_hidden(k4_tarski('#skF_5'(A_114, B_115), '#skF_6'(A_114, B_115)), '#skF_8') | ~r1_tarski(A_114, '#skF_9') | r1_tarski(A_114, B_115) | ~v1_relat_1(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_396])).
% 5.40/2.00  tff(c_243, plain, (![D_94, E_95, A_96, B_97]: (r2_hidden(k4_tarski(D_94, E_95), k7_relat_1(A_96, B_97)) | ~r2_hidden(k4_tarski(D_94, E_95), A_96) | ~r2_hidden(D_94, B_97) | ~v1_relat_1(k7_relat_1(A_96, B_97)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.40/2.00  tff(c_22, plain, (![A_20, B_30]: (~r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_30) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.40/2.00  tff(c_3051, plain, (![A_266, A_267, B_268]: (r1_tarski(A_266, k7_relat_1(A_267, B_268)) | ~v1_relat_1(A_266) | ~r2_hidden(k4_tarski('#skF_5'(A_266, k7_relat_1(A_267, B_268)), '#skF_6'(A_266, k7_relat_1(A_267, B_268))), A_267) | ~r2_hidden('#skF_5'(A_266, k7_relat_1(A_267, B_268)), B_268) | ~v1_relat_1(k7_relat_1(A_267, B_268)) | ~v1_relat_1(A_267))), inference(resolution, [status(thm)], [c_243, c_22])).
% 5.40/2.00  tff(c_3107, plain, (![A_114, B_268]: (~r2_hidden('#skF_5'(A_114, k7_relat_1('#skF_8', B_268)), B_268) | ~v1_relat_1(k7_relat_1('#skF_8', B_268)) | ~v1_relat_1('#skF_8') | ~r1_tarski(A_114, '#skF_9') | r1_tarski(A_114, k7_relat_1('#skF_8', B_268)) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_412, c_3051])).
% 5.40/2.00  tff(c_3269, plain, (![A_273, B_274]: (~r2_hidden('#skF_5'(A_273, k7_relat_1('#skF_8', B_274)), B_274) | ~v1_relat_1(k7_relat_1('#skF_8', B_274)) | ~r1_tarski(A_273, '#skF_9') | r1_tarski(A_273, k7_relat_1('#skF_8', B_274)) | ~v1_relat_1(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3107])).
% 5.40/2.00  tff(c_3337, plain, (~v1_relat_1(k7_relat_1('#skF_8', '#skF_7')) | ~r1_tarski('#skF_9', '#skF_9') | ~v1_relat_1('#skF_9') | r1_tarski('#skF_9', k7_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_185, c_3269])).
% 5.40/2.00  tff(c_3371, plain, (~v1_relat_1(k7_relat_1('#skF_8', '#skF_7')) | r1_tarski('#skF_9', k7_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_111, c_3337])).
% 5.40/2.00  tff(c_3372, plain, (~v1_relat_1(k7_relat_1('#skF_8', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_34, c_3371])).
% 5.40/2.00  tff(c_3377, plain, (~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_3372])).
% 5.40/2.00  tff(c_3381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3377])).
% 5.40/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.00  
% 5.40/2.00  Inference rules
% 5.40/2.00  ----------------------
% 5.40/2.00  #Ref     : 0
% 5.40/2.00  #Sup     : 705
% 5.40/2.00  #Fact    : 2
% 5.40/2.00  #Define  : 0
% 5.40/2.00  #Split   : 7
% 5.40/2.00  #Chain   : 0
% 5.40/2.00  #Close   : 0
% 5.40/2.00  
% 5.40/2.00  Ordering : KBO
% 5.40/2.00  
% 5.40/2.00  Simplification rules
% 5.40/2.00  ----------------------
% 5.40/2.00  #Subsume      : 195
% 5.40/2.00  #Demod        : 713
% 5.40/2.00  #Tautology    : 173
% 5.40/2.00  #SimpNegUnit  : 1
% 5.40/2.00  #BackRed      : 1
% 5.40/2.00  
% 5.40/2.00  #Partial instantiations: 0
% 5.40/2.00  #Strategies tried      : 1
% 5.40/2.00  
% 5.40/2.00  Timing (in seconds)
% 5.40/2.00  ----------------------
% 5.40/2.00  Preprocessing        : 0.29
% 5.40/2.00  Parsing              : 0.15
% 5.40/2.00  CNF conversion       : 0.02
% 5.40/2.00  Main loop            : 0.93
% 5.40/2.00  Inferencing          : 0.33
% 5.40/2.00  Reduction            : 0.27
% 5.40/2.00  Demodulation         : 0.19
% 5.40/2.00  BG Simplification    : 0.03
% 5.40/2.00  Subsumption          : 0.24
% 5.40/2.00  Abstraction          : 0.04
% 5.40/2.00  MUC search           : 0.00
% 5.40/2.00  Cooper               : 0.00
% 5.40/2.00  Total                : 1.25
% 5.40/2.00  Index Insertion      : 0.00
% 5.40/2.00  Index Deletion       : 0.00
% 5.40/2.00  Index Matching       : 0.00
% 5.40/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
