%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:27 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 124 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_finset_1 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_26,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_79,plain,(
    ! [A_27,B_28,C_29] :
      ( v1_finset_1('#skF_1'(A_27,B_28,C_29))
      | ~ r1_tarski(A_27,k2_zfmisc_1(B_28,C_29))
      | ~ v1_finset_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,
    ( v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_93,plain,(
    v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski('#skF_1'(A_10,B_11,C_12),B_11)
      | ~ r1_tarski(A_10,k2_zfmisc_1(B_11,C_12))
      | ~ v1_finset_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski('#skF_2'(A_10,B_11,C_12),C_12)
      | ~ r1_tarski(A_10,k2_zfmisc_1(B_11,C_12))
      | ~ v1_finset_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_244,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k2_zfmisc_1('#skF_1'(A_57,B_58,C_59),'#skF_2'(A_57,B_58,C_59)))
      | ~ r1_tarski(A_57,k2_zfmisc_1(B_58,C_59))
      | ~ v1_finset_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_40,C_41,B_42,D_43] :
      ( r1_tarski(k2_zfmisc_1(A_40,C_41),k2_zfmisc_1(B_42,D_43))
      | ~ r1_tarski(C_41,D_43)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [A_3,B_42,A_40,C_41,D_43] :
      ( r1_tarski(A_3,k2_zfmisc_1(B_42,D_43))
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_40,C_41))
      | ~ r1_tarski(C_41,D_43)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(resolution,[status(thm)],[c_126,c_8])).

tff(c_3700,plain,(
    ! [C_460,B_456,A_458,D_457,B_459] :
      ( r1_tarski(A_458,k2_zfmisc_1(B_459,D_457))
      | ~ r1_tarski('#skF_2'(A_458,B_456,C_460),D_457)
      | ~ r1_tarski('#skF_1'(A_458,B_456,C_460),B_459)
      | ~ r1_tarski(A_458,k2_zfmisc_1(B_456,C_460))
      | ~ v1_finset_1(A_458) ) ),
    inference(resolution,[status(thm)],[c_244,c_147])).

tff(c_3727,plain,(
    ! [A_461,B_462,C_463,B_464] :
      ( r1_tarski(A_461,k2_zfmisc_1(B_462,C_463))
      | ~ r1_tarski('#skF_1'(A_461,B_464,C_463),B_462)
      | ~ r1_tarski(A_461,k2_zfmisc_1(B_464,C_463))
      | ~ v1_finset_1(A_461) ) ),
    inference(resolution,[status(thm)],[c_14,c_3700])).

tff(c_3761,plain,(
    ! [A_465,B_466,C_467] :
      ( r1_tarski(A_465,k2_zfmisc_1('#skF_1'(A_465,B_466,C_467),C_467))
      | ~ r1_tarski(A_465,k2_zfmisc_1(B_466,C_467))
      | ~ v1_finset_1(A_465) ) ),
    inference(resolution,[status(thm)],[c_6,c_3727])).

tff(c_22,plain,(
    ! [D_16] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_16,'#skF_5'))
      | ~ r1_tarski(D_16,'#skF_4')
      | ~ v1_finset_1(D_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3886,plain,(
    ! [B_466] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_466,'#skF_5'),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_466,'#skF_5'))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_466,'#skF_5'))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3761,c_22])).

tff(c_4079,plain,(
    ! [B_478] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_478,'#skF_5'),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_478,'#skF_5'))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_478,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3886])).

tff(c_4083,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_4079])).

tff(c_4087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_93,c_4083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:26:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.67  
% 8.09/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.67  %$ r1_tarski > v1_finset_1 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 8.09/2.67  
% 8.09/2.67  %Foreground sorts:
% 8.09/2.67  
% 8.09/2.67  
% 8.09/2.67  %Background operators:
% 8.09/2.67  
% 8.09/2.67  
% 8.09/2.67  %Foreground operators:
% 8.09/2.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.09/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.09/2.67  tff('#skF_5', type, '#skF_5': $i).
% 8.09/2.67  tff('#skF_3', type, '#skF_3': $i).
% 8.09/2.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.09/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.09/2.67  tff('#skF_4', type, '#skF_4': $i).
% 8.09/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/2.67  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 8.09/2.67  
% 8.16/2.68  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 8.16/2.68  tff(f_60, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 8.16/2.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.16/2.68  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 8.16/2.68  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.16/2.68  tff(c_26, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.16/2.68  tff(c_24, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.16/2.68  tff(c_79, plain, (![A_27, B_28, C_29]: (v1_finset_1('#skF_1'(A_27, B_28, C_29)) | ~r1_tarski(A_27, k2_zfmisc_1(B_28, C_29)) | ~v1_finset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.16/2.68  tff(c_85, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_79])).
% 8.16/2.68  tff(c_93, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_85])).
% 8.16/2.68  tff(c_18, plain, (![A_10, B_11, C_12]: (r1_tarski('#skF_1'(A_10, B_11, C_12), B_11) | ~r1_tarski(A_10, k2_zfmisc_1(B_11, C_12)) | ~v1_finset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.16/2.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.16/2.68  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski('#skF_2'(A_10, B_11, C_12), C_12) | ~r1_tarski(A_10, k2_zfmisc_1(B_11, C_12)) | ~v1_finset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.16/2.68  tff(c_244, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k2_zfmisc_1('#skF_1'(A_57, B_58, C_59), '#skF_2'(A_57, B_58, C_59))) | ~r1_tarski(A_57, k2_zfmisc_1(B_58, C_59)) | ~v1_finset_1(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.16/2.68  tff(c_126, plain, (![A_40, C_41, B_42, D_43]: (r1_tarski(k2_zfmisc_1(A_40, C_41), k2_zfmisc_1(B_42, D_43)) | ~r1_tarski(C_41, D_43) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.16/2.68  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.16/2.68  tff(c_147, plain, (![A_3, B_42, A_40, C_41, D_43]: (r1_tarski(A_3, k2_zfmisc_1(B_42, D_43)) | ~r1_tarski(A_3, k2_zfmisc_1(A_40, C_41)) | ~r1_tarski(C_41, D_43) | ~r1_tarski(A_40, B_42))), inference(resolution, [status(thm)], [c_126, c_8])).
% 8.16/2.68  tff(c_3700, plain, (![C_460, B_456, A_458, D_457, B_459]: (r1_tarski(A_458, k2_zfmisc_1(B_459, D_457)) | ~r1_tarski('#skF_2'(A_458, B_456, C_460), D_457) | ~r1_tarski('#skF_1'(A_458, B_456, C_460), B_459) | ~r1_tarski(A_458, k2_zfmisc_1(B_456, C_460)) | ~v1_finset_1(A_458))), inference(resolution, [status(thm)], [c_244, c_147])).
% 8.16/2.68  tff(c_3727, plain, (![A_461, B_462, C_463, B_464]: (r1_tarski(A_461, k2_zfmisc_1(B_462, C_463)) | ~r1_tarski('#skF_1'(A_461, B_464, C_463), B_462) | ~r1_tarski(A_461, k2_zfmisc_1(B_464, C_463)) | ~v1_finset_1(A_461))), inference(resolution, [status(thm)], [c_14, c_3700])).
% 8.16/2.68  tff(c_3761, plain, (![A_465, B_466, C_467]: (r1_tarski(A_465, k2_zfmisc_1('#skF_1'(A_465, B_466, C_467), C_467)) | ~r1_tarski(A_465, k2_zfmisc_1(B_466, C_467)) | ~v1_finset_1(A_465))), inference(resolution, [status(thm)], [c_6, c_3727])).
% 8.16/2.68  tff(c_22, plain, (![D_16]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_16, '#skF_5')) | ~r1_tarski(D_16, '#skF_4') | ~v1_finset_1(D_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.16/2.68  tff(c_3886, plain, (![B_466]: (~r1_tarski('#skF_1'('#skF_3', B_466, '#skF_5'), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_466, '#skF_5')) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_466, '#skF_5')) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_3761, c_22])).
% 8.16/2.68  tff(c_4079, plain, (![B_478]: (~r1_tarski('#skF_1'('#skF_3', B_478, '#skF_5'), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_478, '#skF_5')) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_478, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3886])).
% 8.16/2.68  tff(c_4083, plain, (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_4079])).
% 8.16/2.68  tff(c_4087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_93, c_4083])).
% 8.16/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.16/2.68  
% 8.16/2.68  Inference rules
% 8.16/2.68  ----------------------
% 8.16/2.68  #Ref     : 0
% 8.16/2.68  #Sup     : 1172
% 8.16/2.68  #Fact    : 0
% 8.16/2.68  #Define  : 0
% 8.16/2.68  #Split   : 7
% 8.16/2.68  #Chain   : 0
% 8.16/2.68  #Close   : 0
% 8.16/2.68  
% 8.16/2.68  Ordering : KBO
% 8.16/2.68  
% 8.16/2.68  Simplification rules
% 8.16/2.68  ----------------------
% 8.16/2.68  #Subsume      : 256
% 8.16/2.68  #Demod        : 33
% 8.16/2.68  #Tautology    : 13
% 8.16/2.68  #SimpNegUnit  : 0
% 8.16/2.68  #BackRed      : 0
% 8.16/2.68  
% 8.16/2.68  #Partial instantiations: 0
% 8.16/2.68  #Strategies tried      : 1
% 8.16/2.68  
% 8.16/2.68  Timing (in seconds)
% 8.16/2.68  ----------------------
% 8.16/2.68  Preprocessing        : 0.26
% 8.16/2.68  Parsing              : 0.15
% 8.16/2.68  CNF conversion       : 0.02
% 8.16/2.68  Main loop            : 1.64
% 8.16/2.68  Inferencing          : 0.35
% 8.16/2.68  Reduction            : 0.30
% 8.16/2.68  Demodulation         : 0.20
% 8.16/2.68  BG Simplification    : 0.05
% 8.16/2.68  Subsumption          : 0.84
% 8.16/2.68  Abstraction          : 0.07
% 8.16/2.68  MUC search           : 0.00
% 8.16/2.68  Cooper               : 0.00
% 8.16/2.68  Total                : 1.93
% 8.16/2.68  Index Insertion      : 0.00
% 8.16/2.68  Index Deletion       : 0.00
% 8.16/2.68  Index Matching       : 0.00
% 8.16/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
