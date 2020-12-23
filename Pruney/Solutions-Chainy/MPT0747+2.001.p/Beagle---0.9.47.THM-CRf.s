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
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 150 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 320 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ~ ( ! [B] :
            ( r2_hidden(B,A)
           => v3_ordinal1(B) )
        & ! [B] :
            ( v3_ordinal1(B)
           => ~ r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_ordinal1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_60,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(A_29),A_29)
      | v3_ordinal1('#skF_3'(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [B_20] :
      ( v3_ordinal1(B_20)
      | ~ r2_hidden(B_20,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_30])).

tff(c_69,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_122,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_2'(A_47),A_47)
      | r1_tarski(A_47,'#skF_3'(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_135,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | r1_tarski('#skF_4','#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_122,c_30])).

tff(c_136,plain,(
    r1_tarski('#skF_4','#skF_3'('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_210,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_602,plain,(
    ! [A_105,B_106,B_107] :
      ( r2_hidden('#skF_1'(A_105,B_106),B_107)
      | ~ r1_tarski(A_105,B_107)
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_8,c_210])).

tff(c_669,plain,(
    ! [A_113,B_114] :
      ( v3_ordinal1('#skF_1'(A_113,B_114))
      | ~ r1_tarski(A_113,'#skF_4')
      | r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_602,c_30])).

tff(c_32,plain,(
    ! [B_20] :
      ( r2_hidden(B_20,'#skF_4')
      | ~ v3_ordinal1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_226,plain,(
    ! [B_60,B_61] :
      ( r2_hidden(B_60,B_61)
      | ~ r1_tarski('#skF_4',B_61)
      | ~ v3_ordinal1(B_60) ) ),
    inference(resolution,[status(thm)],[c_32,c_210])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_266,plain,(
    ! [A_3,B_61] :
      ( r1_tarski(A_3,B_61)
      | ~ r1_tarski('#skF_4',B_61)
      | ~ v3_ordinal1('#skF_1'(A_3,B_61)) ) ),
    inference(resolution,[status(thm)],[c_226,c_6])).

tff(c_679,plain,(
    ! [B_115,A_116] :
      ( ~ r1_tarski('#skF_4',B_115)
      | ~ r1_tarski(A_116,'#skF_4')
      | r1_tarski(A_116,B_115) ) ),
    inference(resolution,[status(thm)],[c_669,c_266])).

tff(c_698,plain,(
    ! [A_116] :
      ( ~ r1_tarski(A_116,'#skF_4')
      | r1_tarski(A_116,'#skF_3'('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_136,c_679])).

tff(c_225,plain,(
    ! [B_20,B_58] :
      ( r2_hidden(B_20,B_58)
      | ~ r1_tarski('#skF_4',B_58)
      | ~ v3_ordinal1(B_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_210])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_282,plain,(
    ! [B_64,B_65] :
      ( ~ r2_hidden(B_64,B_65)
      | ~ r1_tarski('#skF_4',B_64)
      | ~ v3_ordinal1(B_65) ) ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_301,plain,(
    ! [B_20,B_58] :
      ( ~ r1_tarski('#skF_4',B_20)
      | ~ v3_ordinal1(B_58)
      | ~ r1_tarski('#skF_4',B_58)
      | ~ v3_ordinal1(B_20) ) ),
    inference(resolution,[status(thm)],[c_225,c_282])).

tff(c_829,plain,(
    ! [B_124] :
      ( ~ r1_tarski('#skF_4',B_124)
      | ~ v3_ordinal1(B_124) ) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_833,plain,
    ( ~ v3_ordinal1('#skF_3'('#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_698,c_829])).

tff(c_858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_69,c_833])).

tff(c_860,plain,(
    ! [B_125] :
      ( ~ v3_ordinal1(B_125)
      | ~ r1_tarski('#skF_4',B_125) ) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_864,plain,
    ( ~ v3_ordinal1('#skF_3'('#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_698,c_860])).

tff(c_889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_69,c_864])).

tff(c_890,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ v3_ordinal1('#skF_2'(A_16))
      | r1_tarski(A_16,'#skF_3'(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_891,plain,(
    ~ r1_tarski('#skF_4','#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_899,plain,(
    ~ v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_891])).

tff(c_903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_899])).

tff(c_905,plain,(
    ~ v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_904,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v3_ordinal1('#skF_2'(A_16))
      | v3_ordinal1('#skF_3'(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_909,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_904,c_26])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_905,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.93  
% 3.56/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.94  %$ r2_hidden > r1_tarski > m1_subset_1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.56/1.94  
% 3.56/1.94  %Foreground sorts:
% 3.56/1.94  
% 3.56/1.94  
% 3.56/1.94  %Background operators:
% 3.56/1.94  
% 3.56/1.94  
% 3.56/1.94  %Foreground operators:
% 3.56/1.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.56/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.94  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.56/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.56/1.94  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.94  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.56/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.56/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.94  
% 3.56/1.96  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.56/1.96  tff(f_68, axiom, (![A]: ~((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) & (![B]: (v3_ordinal1(B) => ~r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_ordinal1)).
% 3.56/1.96  tff(f_75, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 3.56/1.96  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.56/1.96  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.96  tff(c_103, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.96  tff(c_112, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_103])).
% 3.56/1.96  tff(c_60, plain, (![A_29]: (r2_hidden('#skF_2'(A_29), A_29) | v3_ordinal1('#skF_3'(A_29)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.96  tff(c_30, plain, (![B_20]: (v3_ordinal1(B_20) | ~r2_hidden(B_20, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.96  tff(c_68, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_30])).
% 3.56/1.96  tff(c_69, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 3.56/1.96  tff(c_122, plain, (![A_47]: (r2_hidden('#skF_2'(A_47), A_47) | r1_tarski(A_47, '#skF_3'(A_47)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.96  tff(c_135, plain, (v3_ordinal1('#skF_2'('#skF_4')) | r1_tarski('#skF_4', '#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_122, c_30])).
% 3.56/1.96  tff(c_136, plain, (r1_tarski('#skF_4', '#skF_3'('#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 3.56/1.96  tff(c_210, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.96  tff(c_602, plain, (![A_105, B_106, B_107]: (r2_hidden('#skF_1'(A_105, B_106), B_107) | ~r1_tarski(A_105, B_107) | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_8, c_210])).
% 3.56/1.96  tff(c_669, plain, (![A_113, B_114]: (v3_ordinal1('#skF_1'(A_113, B_114)) | ~r1_tarski(A_113, '#skF_4') | r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_602, c_30])).
% 3.56/1.96  tff(c_32, plain, (![B_20]: (r2_hidden(B_20, '#skF_4') | ~v3_ordinal1(B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.56/1.96  tff(c_226, plain, (![B_60, B_61]: (r2_hidden(B_60, B_61) | ~r1_tarski('#skF_4', B_61) | ~v3_ordinal1(B_60))), inference(resolution, [status(thm)], [c_32, c_210])).
% 3.56/1.96  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.96  tff(c_266, plain, (![A_3, B_61]: (r1_tarski(A_3, B_61) | ~r1_tarski('#skF_4', B_61) | ~v3_ordinal1('#skF_1'(A_3, B_61)))), inference(resolution, [status(thm)], [c_226, c_6])).
% 3.56/1.96  tff(c_679, plain, (![B_115, A_116]: (~r1_tarski('#skF_4', B_115) | ~r1_tarski(A_116, '#skF_4') | r1_tarski(A_116, B_115))), inference(resolution, [status(thm)], [c_669, c_266])).
% 3.56/1.96  tff(c_698, plain, (![A_116]: (~r1_tarski(A_116, '#skF_4') | r1_tarski(A_116, '#skF_3'('#skF_4')))), inference(resolution, [status(thm)], [c_136, c_679])).
% 3.56/1.96  tff(c_225, plain, (![B_20, B_58]: (r2_hidden(B_20, B_58) | ~r1_tarski('#skF_4', B_58) | ~v3_ordinal1(B_20))), inference(resolution, [status(thm)], [c_32, c_210])).
% 3.56/1.96  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.56/1.96  tff(c_282, plain, (![B_64, B_65]: (~r2_hidden(B_64, B_65) | ~r1_tarski('#skF_4', B_64) | ~v3_ordinal1(B_65))), inference(resolution, [status(thm)], [c_226, c_2])).
% 3.56/1.96  tff(c_301, plain, (![B_20, B_58]: (~r1_tarski('#skF_4', B_20) | ~v3_ordinal1(B_58) | ~r1_tarski('#skF_4', B_58) | ~v3_ordinal1(B_20))), inference(resolution, [status(thm)], [c_225, c_282])).
% 3.56/1.96  tff(c_829, plain, (![B_124]: (~r1_tarski('#skF_4', B_124) | ~v3_ordinal1(B_124))), inference(splitLeft, [status(thm)], [c_301])).
% 3.56/1.96  tff(c_833, plain, (~v3_ordinal1('#skF_3'('#skF_4')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_698, c_829])).
% 3.56/1.96  tff(c_858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_69, c_833])).
% 3.56/1.96  tff(c_860, plain, (![B_125]: (~v3_ordinal1(B_125) | ~r1_tarski('#skF_4', B_125))), inference(splitRight, [status(thm)], [c_301])).
% 3.56/1.96  tff(c_864, plain, (~v3_ordinal1('#skF_3'('#skF_4')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_698, c_860])).
% 3.56/1.96  tff(c_889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_69, c_864])).
% 3.56/1.96  tff(c_890, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 3.56/1.96  tff(c_22, plain, (![A_16]: (~v3_ordinal1('#skF_2'(A_16)) | r1_tarski(A_16, '#skF_3'(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.96  tff(c_891, plain, (~r1_tarski('#skF_4', '#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 3.56/1.96  tff(c_899, plain, (~v3_ordinal1('#skF_2'('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_891])).
% 3.56/1.96  tff(c_903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_890, c_899])).
% 3.56/1.96  tff(c_905, plain, (~v3_ordinal1('#skF_3'('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 3.56/1.96  tff(c_904, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 3.56/1.96  tff(c_26, plain, (![A_16]: (~v3_ordinal1('#skF_2'(A_16)) | v3_ordinal1('#skF_3'(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.96  tff(c_909, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_904, c_26])).
% 3.56/1.96  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_905, c_909])).
% 3.56/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.96  
% 3.56/1.96  Inference rules
% 3.56/1.96  ----------------------
% 3.56/1.96  #Ref     : 0
% 3.56/1.96  #Sup     : 177
% 3.56/1.96  #Fact    : 0
% 3.56/1.96  #Define  : 0
% 3.56/1.96  #Split   : 4
% 3.56/1.96  #Chain   : 0
% 3.56/1.96  #Close   : 0
% 3.56/1.96  
% 3.56/1.96  Ordering : KBO
% 3.56/1.96  
% 3.56/1.96  Simplification rules
% 3.56/1.96  ----------------------
% 3.56/1.96  #Subsume      : 18
% 3.56/1.96  #Demod        : 15
% 3.56/1.96  #Tautology    : 13
% 3.56/1.96  #SimpNegUnit  : 11
% 3.56/1.96  #BackRed      : 0
% 3.56/1.96  
% 3.56/1.96  #Partial instantiations: 0
% 3.56/1.96  #Strategies tried      : 1
% 3.56/1.96  
% 3.56/1.96  Timing (in seconds)
% 3.56/1.96  ----------------------
% 3.56/1.96  Preprocessing        : 0.43
% 3.56/1.96  Parsing              : 0.24
% 3.56/1.96  CNF conversion       : 0.03
% 3.56/1.96  Main loop            : 0.63
% 3.56/1.96  Inferencing          : 0.25
% 3.56/1.96  Reduction            : 0.15
% 3.56/1.96  Demodulation         : 0.10
% 3.56/1.97  BG Simplification    : 0.03
% 3.56/1.97  Subsumption          : 0.15
% 3.56/1.97  Abstraction          : 0.02
% 3.56/1.97  MUC search           : 0.00
% 3.56/1.97  Cooper               : 0.00
% 3.56/1.97  Total                : 1.12
% 3.56/1.97  Index Insertion      : 0.00
% 3.56/1.97  Index Deletion       : 0.00
% 3.56/1.97  Index Matching       : 0.00
% 3.56/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
