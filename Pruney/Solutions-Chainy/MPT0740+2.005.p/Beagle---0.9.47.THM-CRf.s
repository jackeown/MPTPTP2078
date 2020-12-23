%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:05 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 244 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_60,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_34,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    ! [A_27] :
      ( v3_ordinal1(k1_ordinal1(A_27))
      | ~ v3_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_35,plain,(
    ! [A_28] :
      ( v1_ordinal1(A_28)
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_35])).

tff(c_99,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_2'(A_47,B_48),A_47)
      | r1_tarski(k3_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_16,A_13] :
      ( r1_tarski(B_16,A_13)
      | ~ r2_hidden(B_16,A_13)
      | ~ v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_382,plain,(
    ! [A_91,B_92] :
      ( r1_tarski('#skF_2'(A_91,B_92),A_91)
      | ~ v1_ordinal1(A_91)
      | r1_tarski(k3_tarski(A_91),B_92) ) ),
    inference(resolution,[status(thm)],[c_99,c_18])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r1_tarski('#skF_2'(A_6,B_7),B_7)
      | r1_tarski(k3_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_393,plain,(
    ! [A_91] :
      ( ~ v1_ordinal1(A_91)
      | r1_tarski(k3_tarski(A_91),A_91) ) ),
    inference(resolution,[status(thm)],[c_382,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_13,B_50] :
      ( r2_hidden('#skF_3'(A_13),B_50)
      | ~ r1_tarski(A_13,B_50)
      | v1_ordinal1(A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_155,plain,(
    ! [C_60,B_61,A_62] :
      ( r1_tarski(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(k3_tarski(A_62),B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2854,plain,(
    ! [A_224,B_225,B_226] :
      ( r1_tarski('#skF_3'(A_224),B_225)
      | ~ r1_tarski(k3_tarski(B_226),B_225)
      | ~ r1_tarski(A_224,B_226)
      | v1_ordinal1(A_224) ) ),
    inference(resolution,[status(thm)],[c_119,c_155])).

tff(c_2956,plain,(
    ! [A_227,B_228] :
      ( r1_tarski('#skF_3'(A_227),k3_tarski(B_228))
      | ~ r1_tarski(A_227,B_228)
      | v1_ordinal1(A_227) ) ),
    inference(resolution,[status(thm)],[c_97,c_2854])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ r1_tarski('#skF_3'(A_13),A_13)
      | v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2977,plain,(
    ! [B_229] :
      ( ~ r1_tarski(k3_tarski(B_229),B_229)
      | v1_ordinal1(k3_tarski(B_229)) ) ),
    inference(resolution,[status(thm)],[c_2956,c_20])).

tff(c_2989,plain,(
    ! [A_91] :
      ( v1_ordinal1(k3_tarski(A_91))
      | ~ v1_ordinal1(A_91) ) ),
    inference(resolution,[status(thm)],[c_393,c_2977])).

tff(c_24,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_208,plain,(
    ! [A_67,C_68,B_69] :
      ( r2_hidden(A_67,C_68)
      | ~ r2_hidden(B_69,C_68)
      | ~ r1_tarski(A_67,B_69)
      | ~ v3_ordinal1(C_68)
      | ~ v3_ordinal1(B_69)
      | ~ v1_ordinal1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1376,plain,(
    ! [A_158,A_159] :
      ( r2_hidden(A_158,k1_ordinal1(A_159))
      | ~ r1_tarski(A_158,A_159)
      | ~ v3_ordinal1(k1_ordinal1(A_159))
      | ~ v3_ordinal1(A_159)
      | ~ v1_ordinal1(A_158) ) ),
    inference(resolution,[status(thm)],[c_24,c_208])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( v3_ordinal1(A_25)
      | ~ r2_hidden(A_25,B_26)
      | ~ v3_ordinal1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1610,plain,(
    ! [A_171,A_172] :
      ( v3_ordinal1(A_171)
      | ~ r1_tarski(A_171,A_172)
      | ~ v3_ordinal1(k1_ordinal1(A_172))
      | ~ v3_ordinal1(A_172)
      | ~ v1_ordinal1(A_171) ) ),
    inference(resolution,[status(thm)],[c_1376,c_28])).

tff(c_5059,plain,(
    ! [A_279] :
      ( v3_ordinal1(k3_tarski(A_279))
      | ~ v3_ordinal1(k1_ordinal1(A_279))
      | ~ v3_ordinal1(A_279)
      | ~ v1_ordinal1(k3_tarski(A_279))
      | ~ v1_ordinal1(A_279) ) ),
    inference(resolution,[status(thm)],[c_393,c_1610])).

tff(c_32,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5113,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1(k3_tarski('#skF_4'))
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5059,c_32])).

tff(c_5133,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_34,c_5113])).

tff(c_5134,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5133])).

tff(c_5140,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2989,c_5134])).

tff(c_5147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_5140])).

tff(c_5148,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5133])).

tff(c_5152,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_5148])).

tff(c_5156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:11:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.24  
% 5.80/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.25  %$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 5.80/2.25  
% 5.80/2.25  %Foreground sorts:
% 5.80/2.25  
% 5.80/2.25  
% 5.80/2.25  %Background operators:
% 5.80/2.25  
% 5.80/2.25  
% 5.80/2.25  %Foreground operators:
% 5.80/2.25  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.80/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.25  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 5.80/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.25  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.80/2.25  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 5.80/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.80/2.25  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.25  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.80/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.80/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.80/2.25  
% 5.80/2.26  tff(f_89, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 5.80/2.26  tff(f_84, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.80/2.26  tff(f_51, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 5.80/2.26  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 5.80/2.26  tff(f_58, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 5.80/2.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.80/2.26  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 5.80/2.26  tff(f_60, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.80/2.26  tff(f_74, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 5.80/2.26  tff(f_80, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 5.80/2.26  tff(c_34, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.80/2.26  tff(c_30, plain, (![A_27]: (v3_ordinal1(k1_ordinal1(A_27)) | ~v3_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.80/2.26  tff(c_35, plain, (![A_28]: (v1_ordinal1(A_28) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.26  tff(c_39, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_35])).
% 5.80/2.26  tff(c_99, plain, (![A_47, B_48]: (r2_hidden('#skF_2'(A_47, B_48), A_47) | r1_tarski(k3_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.80/2.26  tff(c_18, plain, (![B_16, A_13]: (r1_tarski(B_16, A_13) | ~r2_hidden(B_16, A_13) | ~v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.80/2.26  tff(c_382, plain, (![A_91, B_92]: (r1_tarski('#skF_2'(A_91, B_92), A_91) | ~v1_ordinal1(A_91) | r1_tarski(k3_tarski(A_91), B_92))), inference(resolution, [status(thm)], [c_99, c_18])).
% 5.80/2.26  tff(c_8, plain, (![A_6, B_7]: (~r1_tarski('#skF_2'(A_6, B_7), B_7) | r1_tarski(k3_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.80/2.26  tff(c_393, plain, (![A_91]: (~v1_ordinal1(A_91) | r1_tarski(k3_tarski(A_91), A_91))), inference(resolution, [status(thm)], [c_382, c_8])).
% 5.80/2.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.26  tff(c_92, plain, (![A_44, B_45]: (~r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.26  tff(c_97, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_92])).
% 5.80/2.26  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.80/2.26  tff(c_108, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.26  tff(c_119, plain, (![A_13, B_50]: (r2_hidden('#skF_3'(A_13), B_50) | ~r1_tarski(A_13, B_50) | v1_ordinal1(A_13))), inference(resolution, [status(thm)], [c_22, c_108])).
% 5.80/2.26  tff(c_155, plain, (![C_60, B_61, A_62]: (r1_tarski(C_60, B_61) | ~r2_hidden(C_60, A_62) | ~r1_tarski(k3_tarski(A_62), B_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.26  tff(c_2854, plain, (![A_224, B_225, B_226]: (r1_tarski('#skF_3'(A_224), B_225) | ~r1_tarski(k3_tarski(B_226), B_225) | ~r1_tarski(A_224, B_226) | v1_ordinal1(A_224))), inference(resolution, [status(thm)], [c_119, c_155])).
% 5.80/2.26  tff(c_2956, plain, (![A_227, B_228]: (r1_tarski('#skF_3'(A_227), k3_tarski(B_228)) | ~r1_tarski(A_227, B_228) | v1_ordinal1(A_227))), inference(resolution, [status(thm)], [c_97, c_2854])).
% 5.80/2.26  tff(c_20, plain, (![A_13]: (~r1_tarski('#skF_3'(A_13), A_13) | v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.80/2.26  tff(c_2977, plain, (![B_229]: (~r1_tarski(k3_tarski(B_229), B_229) | v1_ordinal1(k3_tarski(B_229)))), inference(resolution, [status(thm)], [c_2956, c_20])).
% 5.80/2.26  tff(c_2989, plain, (![A_91]: (v1_ordinal1(k3_tarski(A_91)) | ~v1_ordinal1(A_91))), inference(resolution, [status(thm)], [c_393, c_2977])).
% 5.80/2.26  tff(c_24, plain, (![A_17]: (r2_hidden(A_17, k1_ordinal1(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.80/2.26  tff(c_208, plain, (![A_67, C_68, B_69]: (r2_hidden(A_67, C_68) | ~r2_hidden(B_69, C_68) | ~r1_tarski(A_67, B_69) | ~v3_ordinal1(C_68) | ~v3_ordinal1(B_69) | ~v1_ordinal1(A_67))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.26  tff(c_1376, plain, (![A_158, A_159]: (r2_hidden(A_158, k1_ordinal1(A_159)) | ~r1_tarski(A_158, A_159) | ~v3_ordinal1(k1_ordinal1(A_159)) | ~v3_ordinal1(A_159) | ~v1_ordinal1(A_158))), inference(resolution, [status(thm)], [c_24, c_208])).
% 5.80/2.26  tff(c_28, plain, (![A_25, B_26]: (v3_ordinal1(A_25) | ~r2_hidden(A_25, B_26) | ~v3_ordinal1(B_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.80/2.26  tff(c_1610, plain, (![A_171, A_172]: (v3_ordinal1(A_171) | ~r1_tarski(A_171, A_172) | ~v3_ordinal1(k1_ordinal1(A_172)) | ~v3_ordinal1(A_172) | ~v1_ordinal1(A_171))), inference(resolution, [status(thm)], [c_1376, c_28])).
% 5.80/2.26  tff(c_5059, plain, (![A_279]: (v3_ordinal1(k3_tarski(A_279)) | ~v3_ordinal1(k1_ordinal1(A_279)) | ~v3_ordinal1(A_279) | ~v1_ordinal1(k3_tarski(A_279)) | ~v1_ordinal1(A_279))), inference(resolution, [status(thm)], [c_393, c_1610])).
% 5.80/2.26  tff(c_32, plain, (~v3_ordinal1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.80/2.26  tff(c_5113, plain, (~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_4') | ~v1_ordinal1(k3_tarski('#skF_4')) | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_5059, c_32])).
% 5.80/2.26  tff(c_5133, plain, (~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v1_ordinal1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_34, c_5113])).
% 5.80/2.26  tff(c_5134, plain, (~v1_ordinal1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_5133])).
% 5.80/2.26  tff(c_5140, plain, (~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_2989, c_5134])).
% 5.80/2.26  tff(c_5147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_5140])).
% 5.80/2.26  tff(c_5148, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_5133])).
% 5.80/2.26  tff(c_5152, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_5148])).
% 5.80/2.26  tff(c_5156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_5152])).
% 5.80/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.26  
% 5.80/2.26  Inference rules
% 5.80/2.26  ----------------------
% 5.80/2.26  #Ref     : 0
% 5.80/2.26  #Sup     : 1189
% 5.80/2.26  #Fact    : 0
% 5.80/2.26  #Define  : 0
% 5.80/2.26  #Split   : 1
% 5.80/2.26  #Chain   : 0
% 5.80/2.26  #Close   : 0
% 5.80/2.26  
% 5.80/2.26  Ordering : KBO
% 5.80/2.26  
% 5.80/2.26  Simplification rules
% 5.80/2.26  ----------------------
% 5.80/2.26  #Subsume      : 68
% 5.80/2.26  #Demod        : 27
% 5.80/2.26  #Tautology    : 27
% 5.80/2.26  #SimpNegUnit  : 0
% 5.80/2.26  #BackRed      : 0
% 5.80/2.26  
% 5.80/2.26  #Partial instantiations: 0
% 5.80/2.26  #Strategies tried      : 1
% 5.80/2.26  
% 5.80/2.26  Timing (in seconds)
% 5.80/2.26  ----------------------
% 5.80/2.26  Preprocessing        : 0.43
% 5.80/2.26  Parsing              : 0.26
% 5.80/2.26  CNF conversion       : 0.03
% 5.80/2.26  Main loop            : 1.07
% 5.80/2.26  Inferencing          : 0.35
% 5.80/2.26  Reduction            : 0.28
% 5.80/2.26  Demodulation         : 0.19
% 5.80/2.26  BG Simplification    : 0.04
% 5.80/2.26  Subsumption          : 0.32
% 5.80/2.26  Abstraction          : 0.05
% 5.80/2.26  MUC search           : 0.00
% 5.80/2.27  Cooper               : 0.00
% 5.80/2.27  Total                : 1.53
% 5.80/2.27  Index Insertion      : 0.00
% 5.80/2.27  Index Deletion       : 0.00
% 5.80/2.27  Index Matching       : 0.00
% 5.80/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
