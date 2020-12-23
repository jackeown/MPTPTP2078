%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 241 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 548 expanded)
%              Number of equality atoms :   25 ( 128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(f_51,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [C_68,D_69,A_70] :
      ( r2_hidden(C_68,D_69)
      | ~ r2_hidden(D_69,A_70)
      | ~ r2_hidden(C_68,k1_setfam_1(A_70))
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,(
    ! [C_71,A_72] :
      ( r2_hidden(C_71,'#skF_2'(A_72))
      | ~ r2_hidden(C_71,k1_setfam_1(A_72))
      | k1_xboole_0 = A_72 ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_554,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(k1_setfam_1(A_114),B_115),'#skF_2'(A_114))
      | k1_xboole_0 = A_114
      | r1_tarski(k1_setfam_1(A_114),B_115) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_592,plain,(
    ! [A_118] :
      ( k1_xboole_0 = A_118
      | r1_tarski(k1_setfam_1(A_118),'#skF_2'(A_118)) ) ),
    inference(resolution,[status(thm)],[c_554,c_4])).

tff(c_71,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_1,B_2,B_53] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_53)
      | ~ r1_tarski(A_1,B_53)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_82,plain,(
    ! [C_57,A_58,D_59] :
      ( r2_hidden(C_57,k3_tarski(A_58))
      | ~ r2_hidden(D_59,A_58)
      | ~ r2_hidden(C_57,D_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [C_60,A_61] :
      ( r2_hidden(C_60,k3_tarski(A_61))
      | ~ r2_hidden(C_60,'#skF_2'(A_61))
      | k1_xboole_0 = A_61 ) ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_420,plain,(
    ! [A_97,A_98] :
      ( r1_tarski(A_97,k3_tarski(A_98))
      | ~ r2_hidden('#skF_1'(A_97,k3_tarski(A_98)),'#skF_2'(A_98))
      | k1_xboole_0 = A_98 ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_449,plain,(
    ! [A_102,A_103] :
      ( k1_xboole_0 = A_102
      | ~ r1_tarski(A_103,'#skF_2'(A_102))
      | r1_tarski(A_103,k3_tarski(A_102)) ) ),
    inference(resolution,[status(thm)],[c_76,c_420])).

tff(c_52,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_11'),k3_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_464,plain,
    ( k1_xboole_0 = '#skF_11'
    | ~ r1_tarski(k1_setfam_1('#skF_11'),'#skF_2'('#skF_11')) ),
    inference(resolution,[status(thm)],[c_449,c_52])).

tff(c_466,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_11'),'#skF_2'('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_601,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_592,c_466])).

tff(c_50,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_629,plain,(
    k1_setfam_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_601,c_50])).

tff(c_28,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_628,plain,(
    k3_tarski('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_601,c_28])).

tff(c_634,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_11'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_52])).

tff(c_653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_629,c_634])).

tff(c_654,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_682,plain,(
    k1_setfam_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_654,c_50])).

tff(c_681,plain,(
    k3_tarski('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_654,c_28])).

tff(c_687,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_11'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_52])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_682,c_687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:34:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.36  
% 2.71/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.36  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 2.71/1.36  
% 2.71/1.36  %Foreground sorts:
% 2.71/1.36  
% 2.71/1.36  
% 2.71/1.36  %Background operators:
% 2.71/1.36  
% 2.71/1.36  
% 2.71/1.36  %Foreground operators:
% 2.71/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.71/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.36  tff('#skF_11', type, '#skF_11': $i).
% 2.71/1.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.71/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.71/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.36  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.71/1.36  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.71/1.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.71/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.71/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.36  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.71/1.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.71/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.71/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.71/1.36  
% 2.71/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.37  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.71/1.37  tff(f_70, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.71/1.37  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.71/1.37  tff(f_73, negated_conjecture, ~(![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 2.71/1.37  tff(f_51, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.71/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_64, plain, (![A_49, B_50]: (~r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_69, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_64])).
% 2.71/1.37  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.71/1.37  tff(c_145, plain, (![C_68, D_69, A_70]: (r2_hidden(C_68, D_69) | ~r2_hidden(D_69, A_70) | ~r2_hidden(C_68, k1_setfam_1(A_70)) | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.37  tff(c_172, plain, (![C_71, A_72]: (r2_hidden(C_71, '#skF_2'(A_72)) | ~r2_hidden(C_71, k1_setfam_1(A_72)) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_8, c_145])).
% 2.71/1.37  tff(c_554, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(k1_setfam_1(A_114), B_115), '#skF_2'(A_114)) | k1_xboole_0=A_114 | r1_tarski(k1_setfam_1(A_114), B_115))), inference(resolution, [status(thm)], [c_6, c_172])).
% 2.71/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_592, plain, (![A_118]: (k1_xboole_0=A_118 | r1_tarski(k1_setfam_1(A_118), '#skF_2'(A_118)))), inference(resolution, [status(thm)], [c_554, c_4])).
% 2.71/1.37  tff(c_71, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_76, plain, (![A_1, B_2, B_53]: (r2_hidden('#skF_1'(A_1, B_2), B_53) | ~r1_tarski(A_1, B_53) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_71])).
% 2.71/1.37  tff(c_82, plain, (![C_57, A_58, D_59]: (r2_hidden(C_57, k3_tarski(A_58)) | ~r2_hidden(D_59, A_58) | ~r2_hidden(C_57, D_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.37  tff(c_92, plain, (![C_60, A_61]: (r2_hidden(C_60, k3_tarski(A_61)) | ~r2_hidden(C_60, '#skF_2'(A_61)) | k1_xboole_0=A_61)), inference(resolution, [status(thm)], [c_8, c_82])).
% 2.71/1.37  tff(c_420, plain, (![A_97, A_98]: (r1_tarski(A_97, k3_tarski(A_98)) | ~r2_hidden('#skF_1'(A_97, k3_tarski(A_98)), '#skF_2'(A_98)) | k1_xboole_0=A_98)), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.71/1.37  tff(c_449, plain, (![A_102, A_103]: (k1_xboole_0=A_102 | ~r1_tarski(A_103, '#skF_2'(A_102)) | r1_tarski(A_103, k3_tarski(A_102)))), inference(resolution, [status(thm)], [c_76, c_420])).
% 2.71/1.37  tff(c_52, plain, (~r1_tarski(k1_setfam_1('#skF_11'), k3_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.37  tff(c_464, plain, (k1_xboole_0='#skF_11' | ~r1_tarski(k1_setfam_1('#skF_11'), '#skF_2'('#skF_11'))), inference(resolution, [status(thm)], [c_449, c_52])).
% 2.71/1.37  tff(c_466, plain, (~r1_tarski(k1_setfam_1('#skF_11'), '#skF_2'('#skF_11'))), inference(splitLeft, [status(thm)], [c_464])).
% 2.71/1.37  tff(c_601, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_592, c_466])).
% 2.71/1.37  tff(c_50, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.37  tff(c_629, plain, (k1_setfam_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_601, c_601, c_50])).
% 2.71/1.37  tff(c_28, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.37  tff(c_628, plain, (k3_tarski('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_601, c_601, c_28])).
% 2.71/1.37  tff(c_634, plain, (~r1_tarski(k1_setfam_1('#skF_11'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_628, c_52])).
% 2.71/1.37  tff(c_653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_629, c_634])).
% 2.71/1.37  tff(c_654, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_464])).
% 2.71/1.37  tff(c_682, plain, (k1_setfam_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_654, c_50])).
% 2.71/1.37  tff(c_681, plain, (k3_tarski('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_654, c_654, c_28])).
% 2.71/1.37  tff(c_687, plain, (~r1_tarski(k1_setfam_1('#skF_11'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_52])).
% 2.71/1.37  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_682, c_687])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 151
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 1
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 4
% 2.71/1.37  #Demod        : 102
% 2.71/1.37  #Tautology    : 31
% 2.71/1.37  #SimpNegUnit  : 0
% 2.71/1.37  #BackRed      : 50
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.28
% 2.71/1.37  Parsing              : 0.15
% 2.71/1.37  CNF conversion       : 0.03
% 2.71/1.37  Main loop            : 0.35
% 2.71/1.37  Inferencing          : 0.12
% 2.71/1.37  Reduction            : 0.09
% 2.71/1.37  Demodulation         : 0.06
% 2.71/1.37  BG Simplification    : 0.02
% 2.71/1.37  Subsumption          : 0.09
% 2.71/1.37  Abstraction          : 0.02
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.38  Cooper               : 0.00
% 2.71/1.38  Total                : 0.66
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
