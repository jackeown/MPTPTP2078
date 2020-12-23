%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:55 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 119 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 327 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

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

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [C_41,A_39,B_40] :
      ( k7_relat_1(k7_relat_1(C_41,A_39),B_40) = k7_relat_1(C_41,A_39)
      | ~ r1_tarski(A_39,B_40)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ! [B_52,A_53,C_54] :
      ( r1_tarski(k7_relat_1(B_52,A_53),k7_relat_1(C_54,A_53))
      | ~ r1_tarski(B_52,C_54)
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_465,plain,(
    ! [C_121,A_122,C_123,B_124] :
      ( r1_tarski(k7_relat_1(C_121,A_122),k7_relat_1(C_123,B_124))
      | ~ r1_tarski(k7_relat_1(C_121,A_122),C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(k7_relat_1(C_121,A_122))
      | ~ r1_tarski(A_122,B_124)
      | ~ v1_relat_1(C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_60])).

tff(c_32,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_10','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_476,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_465,c_32])).

tff(c_507,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_38,c_476])).

tff(c_508,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_511,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_508])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_511])).

tff(c_517,plain,(
    v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [D_71,E_72,A_73,B_74] :
      ( r2_hidden(k4_tarski(D_71,E_72),A_73)
      | ~ r2_hidden(k4_tarski(D_71,E_72),k7_relat_1(A_73,B_74))
      | ~ v1_relat_1(k7_relat_1(A_73,B_74))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_650,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_141,B_142),B_143),'#skF_6'(k7_relat_1(A_141,B_142),B_143)),A_141)
      | ~ v1_relat_1(A_141)
      | r1_tarski(k7_relat_1(A_141,B_142),B_143)
      | ~ v1_relat_1(k7_relat_1(A_141,B_142)) ) ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_693,plain,(
    ! [A_144,B_145] :
      ( ~ v1_relat_1(A_144)
      | r1_tarski(k7_relat_1(A_144,B_145),A_144)
      | ~ v1_relat_1(k7_relat_1(A_144,B_145)) ) ),
    inference(resolution,[status(thm)],[c_650,c_22])).

tff(c_36,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ! [C_60,D_61,B_62,A_63] :
      ( r2_hidden(k4_tarski(C_60,D_61),B_62)
      | ~ r2_hidden(k4_tarski(C_60,D_61),A_63)
      | ~ r1_tarski(A_63,B_62)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_68,B_69,B_70] :
      ( r2_hidden(k4_tarski('#skF_5'(A_68,B_69),'#skF_6'(A_68,B_69)),B_70)
      | ~ r1_tarski(A_68,B_70)
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_20,plain,(
    ! [C_35,D_36,B_30,A_20] :
      ( r2_hidden(k4_tarski(C_35,D_36),B_30)
      | ~ r2_hidden(k4_tarski(C_35,D_36),A_20)
      | ~ r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_372,plain,(
    ! [A_103,B_104,B_105,B_106] :
      ( r2_hidden(k4_tarski('#skF_5'(A_103,B_104),'#skF_6'(A_103,B_104)),B_105)
      | ~ r1_tarski(B_106,B_105)
      | ~ v1_relat_1(B_106)
      | ~ r1_tarski(A_103,B_106)
      | r1_tarski(A_103,B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_88,c_20])).

tff(c_378,plain,(
    ! [A_103,B_104] :
      ( r2_hidden(k4_tarski('#skF_5'(A_103,B_104),'#skF_6'(A_103,B_104)),'#skF_10')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_103,'#skF_9')
      | r1_tarski(A_103,B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_36,c_372])).

tff(c_387,plain,(
    ! [A_107,B_108] :
      ( r2_hidden(k4_tarski('#skF_5'(A_107,B_108),'#skF_6'(A_107,B_108)),'#skF_10')
      | ~ r1_tarski(A_107,'#skF_9')
      | r1_tarski(A_107,B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_378])).

tff(c_397,plain,(
    ! [A_107] :
      ( ~ r1_tarski(A_107,'#skF_9')
      | r1_tarski(A_107,'#skF_10')
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_387,c_22])).

tff(c_516,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_520,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_397,c_516])).

tff(c_523,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_520])).

tff(c_699,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_693,c_523])).

tff(c_725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_40,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.51  
% 3.11/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.51  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 3.11/1.51  
% 3.11/1.51  %Foreground sorts:
% 3.11/1.51  
% 3.11/1.51  
% 3.11/1.51  %Background operators:
% 3.11/1.51  
% 3.11/1.51  
% 3.11/1.51  %Foreground operators:
% 3.11/1.51  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.11/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.11/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.11/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.11/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.11/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.11/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.11/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.11/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.11/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.11/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.11/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.11/1.51  
% 3.28/1.53  tff(f_80, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 3.28/1.53  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.28/1.53  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 3.28/1.53  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 3.28/1.53  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 3.28/1.53  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 3.28/1.53  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_26, plain, (![A_37, B_38]: (v1_relat_1(k7_relat_1(A_37, B_38)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.53  tff(c_34, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_38, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_28, plain, (![C_41, A_39, B_40]: (k7_relat_1(k7_relat_1(C_41, A_39), B_40)=k7_relat_1(C_41, A_39) | ~r1_tarski(A_39, B_40) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.28/1.53  tff(c_60, plain, (![B_52, A_53, C_54]: (r1_tarski(k7_relat_1(B_52, A_53), k7_relat_1(C_54, A_53)) | ~r1_tarski(B_52, C_54) | ~v1_relat_1(C_54) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.28/1.53  tff(c_465, plain, (![C_121, A_122, C_123, B_124]: (r1_tarski(k7_relat_1(C_121, A_122), k7_relat_1(C_123, B_124)) | ~r1_tarski(k7_relat_1(C_121, A_122), C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(k7_relat_1(C_121, A_122)) | ~r1_tarski(A_122, B_124) | ~v1_relat_1(C_121))), inference(superposition, [status(thm), theory('equality')], [c_28, c_60])).
% 3.28/1.53  tff(c_32, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_10', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_476, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_10') | ~v1_relat_1('#skF_10') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_465, c_32])).
% 3.28/1.53  tff(c_507, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_10') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_38, c_476])).
% 3.28/1.53  tff(c_508, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_507])).
% 3.28/1.53  tff(c_511, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_508])).
% 3.28/1.53  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_511])).
% 3.28/1.53  tff(c_517, plain, (v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_507])).
% 3.28/1.53  tff(c_24, plain, (![A_20, B_30]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_20) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.53  tff(c_102, plain, (![D_71, E_72, A_73, B_74]: (r2_hidden(k4_tarski(D_71, E_72), A_73) | ~r2_hidden(k4_tarski(D_71, E_72), k7_relat_1(A_73, B_74)) | ~v1_relat_1(k7_relat_1(A_73, B_74)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.53  tff(c_650, plain, (![A_141, B_142, B_143]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_141, B_142), B_143), '#skF_6'(k7_relat_1(A_141, B_142), B_143)), A_141) | ~v1_relat_1(A_141) | r1_tarski(k7_relat_1(A_141, B_142), B_143) | ~v1_relat_1(k7_relat_1(A_141, B_142)))), inference(resolution, [status(thm)], [c_24, c_102])).
% 3.28/1.53  tff(c_22, plain, (![A_20, B_30]: (~r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_30) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.53  tff(c_693, plain, (![A_144, B_145]: (~v1_relat_1(A_144) | r1_tarski(k7_relat_1(A_144, B_145), A_144) | ~v1_relat_1(k7_relat_1(A_144, B_145)))), inference(resolution, [status(thm)], [c_650, c_22])).
% 3.28/1.53  tff(c_36, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.53  tff(c_75, plain, (![C_60, D_61, B_62, A_63]: (r2_hidden(k4_tarski(C_60, D_61), B_62) | ~r2_hidden(k4_tarski(C_60, D_61), A_63) | ~r1_tarski(A_63, B_62) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.53  tff(c_88, plain, (![A_68, B_69, B_70]: (r2_hidden(k4_tarski('#skF_5'(A_68, B_69), '#skF_6'(A_68, B_69)), B_70) | ~r1_tarski(A_68, B_70) | r1_tarski(A_68, B_69) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_24, c_75])).
% 3.28/1.53  tff(c_20, plain, (![C_35, D_36, B_30, A_20]: (r2_hidden(k4_tarski(C_35, D_36), B_30) | ~r2_hidden(k4_tarski(C_35, D_36), A_20) | ~r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.53  tff(c_372, plain, (![A_103, B_104, B_105, B_106]: (r2_hidden(k4_tarski('#skF_5'(A_103, B_104), '#skF_6'(A_103, B_104)), B_105) | ~r1_tarski(B_106, B_105) | ~v1_relat_1(B_106) | ~r1_tarski(A_103, B_106) | r1_tarski(A_103, B_104) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_88, c_20])).
% 3.28/1.53  tff(c_378, plain, (![A_103, B_104]: (r2_hidden(k4_tarski('#skF_5'(A_103, B_104), '#skF_6'(A_103, B_104)), '#skF_10') | ~v1_relat_1('#skF_9') | ~r1_tarski(A_103, '#skF_9') | r1_tarski(A_103, B_104) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_36, c_372])).
% 3.28/1.53  tff(c_387, plain, (![A_107, B_108]: (r2_hidden(k4_tarski('#skF_5'(A_107, B_108), '#skF_6'(A_107, B_108)), '#skF_10') | ~r1_tarski(A_107, '#skF_9') | r1_tarski(A_107, B_108) | ~v1_relat_1(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_378])).
% 3.28/1.53  tff(c_397, plain, (![A_107]: (~r1_tarski(A_107, '#skF_9') | r1_tarski(A_107, '#skF_10') | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_387, c_22])).
% 3.28/1.53  tff(c_516, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_10')), inference(splitRight, [status(thm)], [c_507])).
% 3.28/1.53  tff(c_520, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_397, c_516])).
% 3.28/1.53  tff(c_523, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_520])).
% 3.28/1.53  tff(c_699, plain, (~v1_relat_1('#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_693, c_523])).
% 3.28/1.53  tff(c_725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_517, c_40, c_699])).
% 3.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  Inference rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Ref     : 0
% 3.28/1.53  #Sup     : 183
% 3.28/1.53  #Fact    : 0
% 3.28/1.53  #Define  : 0
% 3.28/1.53  #Split   : 4
% 3.28/1.53  #Chain   : 0
% 3.28/1.53  #Close   : 0
% 3.28/1.53  
% 3.28/1.53  Ordering : KBO
% 3.28/1.53  
% 3.28/1.53  Simplification rules
% 3.28/1.53  ----------------------
% 3.28/1.53  #Subsume      : 19
% 3.28/1.53  #Demod        : 16
% 3.28/1.53  #Tautology    : 24
% 3.28/1.53  #SimpNegUnit  : 0
% 3.28/1.53  #BackRed      : 0
% 3.28/1.53  
% 3.28/1.53  #Partial instantiations: 0
% 3.28/1.53  #Strategies tried      : 1
% 3.28/1.53  
% 3.28/1.53  Timing (in seconds)
% 3.28/1.53  ----------------------
% 3.28/1.53  Preprocessing        : 0.31
% 3.28/1.53  Parsing              : 0.17
% 3.28/1.53  CNF conversion       : 0.03
% 3.28/1.53  Main loop            : 0.40
% 3.28/1.53  Inferencing          : 0.15
% 3.28/1.53  Reduction            : 0.09
% 3.28/1.53  Demodulation         : 0.06
% 3.28/1.53  BG Simplification    : 0.02
% 3.28/1.53  Subsumption          : 0.11
% 3.28/1.53  Abstraction          : 0.02
% 3.28/1.53  MUC search           : 0.00
% 3.28/1.53  Cooper               : 0.00
% 3.28/1.53  Total                : 0.74
% 3.28/1.53  Index Insertion      : 0.00
% 3.28/1.53  Index Deletion       : 0.00
% 3.28/1.53  Index Matching       : 0.00
% 3.28/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
