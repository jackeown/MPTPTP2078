%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:27 EST 2020

% Result     : Theorem 16.55s
% Output     : CNFRefutation 16.55s
% Verified   : 
% Statistics : Number of formulae       :   34 (  47 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 125 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,(
    ! [A_27,B_28,C_29] :
      ( v1_finset_1('#skF_1'(A_27,B_28,C_29))
      | ~ r1_tarski(A_27,k2_zfmisc_1(B_28,C_29))
      | ~ v1_finset_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,
    ( v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_82,plain,(
    v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_76])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski('#skF_2'(A_7,B_8,C_9),C_9)
      | ~ r1_tarski(A_7,k2_zfmisc_1(B_8,C_9))
      | ~ v1_finset_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski('#skF_1'(A_7,B_8,C_9),B_8)
      | ~ r1_tarski(A_7,k2_zfmisc_1(B_8,C_9))
      | ~ v1_finset_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_213,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,k2_zfmisc_1('#skF_1'(A_53,B_54,C_55),'#skF_2'(A_53,B_54,C_55)))
      | ~ r1_tarski(A_53,k2_zfmisc_1(B_54,C_55))
      | ~ v1_finset_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_tarski(k2_zfmisc_1(C_21,A_22),k2_zfmisc_1(C_21,B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_1,C_21,B_23,A_22] :
      ( r1_tarski(A_1,k2_zfmisc_1(C_21,B_23))
      | ~ r1_tarski(A_1,k2_zfmisc_1(C_21,A_22))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_4001,plain,(
    ! [A_342,B_343,C_344,B_345] :
      ( r1_tarski(A_342,k2_zfmisc_1('#skF_1'(A_342,B_343,C_344),B_345))
      | ~ r1_tarski('#skF_2'(A_342,B_343,C_344),B_345)
      | ~ r1_tarski(A_342,k2_zfmisc_1(B_343,C_344))
      | ~ v1_finset_1(A_342) ) ),
    inference(resolution,[status(thm)],[c_213,c_38])).

tff(c_18,plain,(
    ! [D_13] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_13,'#skF_5'))
      | ~ r1_tarski(D_13,'#skF_4')
      | ~ v1_finset_1(D_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4090,plain,(
    ! [B_343,C_344] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_343,C_344),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_343,C_344))
      | ~ r1_tarski('#skF_2'('#skF_3',B_343,C_344),'#skF_5')
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_343,C_344))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4001,c_18])).

tff(c_26927,plain,(
    ! [B_1018,C_1019] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_1018,C_1019),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_1018,C_1019))
      | ~ r1_tarski('#skF_2'('#skF_3',B_1018,C_1019),'#skF_5')
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_1018,C_1019)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4090])).

tff(c_26939,plain,(
    ! [C_9] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_9))
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_4',C_9),'#skF_5')
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_9))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_26927])).

tff(c_26949,plain,(
    ! [C_1020] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_1020))
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_4',C_1020),'#skF_5')
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_1020)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26939])).

tff(c_26961,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_26949])).

tff(c_26971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_82,c_26961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:48:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.55/9.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.55/9.60  
% 16.55/9.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.55/9.60  %$ r1_tarski > v1_finset_1 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 16.55/9.60  
% 16.55/9.60  %Foreground sorts:
% 16.55/9.60  
% 16.55/9.60  
% 16.55/9.60  %Background operators:
% 16.55/9.60  
% 16.55/9.60  
% 16.55/9.60  %Foreground operators:
% 16.55/9.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.55/9.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.55/9.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.55/9.60  tff('#skF_5', type, '#skF_5': $i).
% 16.55/9.60  tff('#skF_3', type, '#skF_3': $i).
% 16.55/9.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.55/9.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.55/9.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.55/9.60  tff('#skF_4', type, '#skF_4': $i).
% 16.55/9.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.55/9.60  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 16.55/9.60  
% 16.55/9.61  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 16.55/9.61  tff(f_54, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 16.55/9.61  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 16.55/9.61  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.55/9.61  tff(c_22, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.55/9.61  tff(c_20, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.55/9.61  tff(c_64, plain, (![A_27, B_28, C_29]: (v1_finset_1('#skF_1'(A_27, B_28, C_29)) | ~r1_tarski(A_27, k2_zfmisc_1(B_28, C_29)) | ~v1_finset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.55/9.61  tff(c_76, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_64])).
% 16.55/9.61  tff(c_82, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_76])).
% 16.55/9.61  tff(c_10, plain, (![A_7, B_8, C_9]: (r1_tarski('#skF_2'(A_7, B_8, C_9), C_9) | ~r1_tarski(A_7, k2_zfmisc_1(B_8, C_9)) | ~v1_finset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.55/9.61  tff(c_14, plain, (![A_7, B_8, C_9]: (r1_tarski('#skF_1'(A_7, B_8, C_9), B_8) | ~r1_tarski(A_7, k2_zfmisc_1(B_8, C_9)) | ~v1_finset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.55/9.61  tff(c_213, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, k2_zfmisc_1('#skF_1'(A_53, B_54, C_55), '#skF_2'(A_53, B_54, C_55))) | ~r1_tarski(A_53, k2_zfmisc_1(B_54, C_55)) | ~v1_finset_1(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.55/9.61  tff(c_35, plain, (![C_21, A_22, B_23]: (r1_tarski(k2_zfmisc_1(C_21, A_22), k2_zfmisc_1(C_21, B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.55/9.61  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.55/9.61  tff(c_38, plain, (![A_1, C_21, B_23, A_22]: (r1_tarski(A_1, k2_zfmisc_1(C_21, B_23)) | ~r1_tarski(A_1, k2_zfmisc_1(C_21, A_22)) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_35, c_2])).
% 16.55/9.61  tff(c_4001, plain, (![A_342, B_343, C_344, B_345]: (r1_tarski(A_342, k2_zfmisc_1('#skF_1'(A_342, B_343, C_344), B_345)) | ~r1_tarski('#skF_2'(A_342, B_343, C_344), B_345) | ~r1_tarski(A_342, k2_zfmisc_1(B_343, C_344)) | ~v1_finset_1(A_342))), inference(resolution, [status(thm)], [c_213, c_38])).
% 16.55/9.61  tff(c_18, plain, (![D_13]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_13, '#skF_5')) | ~r1_tarski(D_13, '#skF_4') | ~v1_finset_1(D_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.55/9.61  tff(c_4090, plain, (![B_343, C_344]: (~r1_tarski('#skF_1'('#skF_3', B_343, C_344), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_343, C_344)) | ~r1_tarski('#skF_2'('#skF_3', B_343, C_344), '#skF_5') | ~r1_tarski('#skF_3', k2_zfmisc_1(B_343, C_344)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_4001, c_18])).
% 16.55/9.61  tff(c_26927, plain, (![B_1018, C_1019]: (~r1_tarski('#skF_1'('#skF_3', B_1018, C_1019), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_1018, C_1019)) | ~r1_tarski('#skF_2'('#skF_3', B_1018, C_1019), '#skF_5') | ~r1_tarski('#skF_3', k2_zfmisc_1(B_1018, C_1019)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4090])).
% 16.55/9.61  tff(c_26939, plain, (![C_9]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_9)) | ~r1_tarski('#skF_2'('#skF_3', '#skF_4', C_9), '#skF_5') | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_9)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_26927])).
% 16.55/9.61  tff(c_26949, plain, (![C_1020]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_1020)) | ~r1_tarski('#skF_2'('#skF_3', '#skF_4', C_1020), '#skF_5') | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_1020)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26939])).
% 16.55/9.61  tff(c_26961, plain, (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_26949])).
% 16.55/9.61  tff(c_26971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_82, c_26961])).
% 16.55/9.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.55/9.61  
% 16.55/9.61  Inference rules
% 16.55/9.61  ----------------------
% 16.55/9.61  #Ref     : 0
% 16.55/9.61  #Sup     : 8282
% 16.55/9.61  #Fact    : 0
% 16.55/9.61  #Define  : 0
% 16.55/9.61  #Split   : 12
% 16.55/9.61  #Chain   : 0
% 16.55/9.61  #Close   : 0
% 16.55/9.61  
% 16.55/9.61  Ordering : KBO
% 16.55/9.61  
% 16.55/9.61  Simplification rules
% 16.55/9.61  ----------------------
% 16.55/9.61  #Subsume      : 1801
% 16.55/9.61  #Demod        : 48
% 16.55/9.61  #Tautology    : 13
% 16.55/9.61  #SimpNegUnit  : 0
% 16.55/9.61  #BackRed      : 0
% 16.55/9.62  
% 16.55/9.62  #Partial instantiations: 0
% 16.55/9.62  #Strategies tried      : 1
% 16.55/9.62  
% 16.55/9.62  Timing (in seconds)
% 16.55/9.62  ----------------------
% 16.64/9.62  Preprocessing        : 0.26
% 16.64/9.62  Parsing              : 0.14
% 16.64/9.62  CNF conversion       : 0.02
% 16.64/9.62  Main loop            : 8.60
% 16.64/9.62  Inferencing          : 0.80
% 16.64/9.62  Reduction            : 0.86
% 16.64/9.62  Demodulation         : 0.51
% 16.64/9.62  BG Simplification    : 0.13
% 16.64/9.62  Subsumption          : 6.42
% 16.64/9.62  Abstraction          : 0.17
% 16.64/9.62  MUC search           : 0.00
% 16.64/9.62  Cooper               : 0.00
% 16.64/9.62  Total                : 8.89
% 16.64/9.62  Index Insertion      : 0.00
% 16.64/9.62  Index Deletion       : 0.00
% 16.64/9.62  Index Matching       : 0.00
% 16.64/9.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
