%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   49 (  90 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 150 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k3_setfam_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k3_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k3_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_573,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_4'(A_155,B_156,C_157),A_155)
      | r2_hidden('#skF_6'(A_155,B_156,C_157),C_157)
      | k3_setfam_1(A_155,B_156) = C_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_55,B_56] : ~ r2_hidden(A_55,k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_1929,plain,(
    ! [A_276,B_277] :
      ( r2_hidden('#skF_4'(A_276,B_277,k1_xboole_0),A_276)
      | k3_setfam_1(A_276,B_277) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_573,c_72])).

tff(c_1959,plain,(
    ! [B_277] : k3_setfam_1(k1_xboole_0,B_277) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1929,c_72])).

tff(c_931,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden('#skF_5'(A_192,B_193,C_194),B_193)
      | r2_hidden('#skF_6'(A_192,B_193,C_194),C_194)
      | k3_setfam_1(A_192,B_193) = C_194 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1333,plain,(
    ! [A_255,B_256] :
      ( r2_hidden('#skF_5'(A_255,B_256,k1_xboole_0),B_256)
      | k3_setfam_1(A_255,B_256) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_931,c_72])).

tff(c_1418,plain,(
    ! [A_255] : k3_setfam_1(A_255,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1333,c_72])).

tff(c_231,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden('#skF_8'(A_97,B_98,k3_setfam_1(A_97,B_98),D_99),B_98)
      | ~ r2_hidden(D_99,k3_setfam_1(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_256,plain,(
    ! [D_99,A_97] : ~ r2_hidden(D_99,k3_setfam_1(A_97,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_231,c_72])).

tff(c_672,plain,(
    ! [A_97,B_156,C_157] :
      ( r2_hidden('#skF_6'(k3_setfam_1(A_97,k1_xboole_0),B_156,C_157),C_157)
      | k3_setfam_1(k3_setfam_1(A_97,k1_xboole_0),B_156) = C_157 ) ),
    inference(resolution,[status(thm)],[c_573,c_256])).

tff(c_2096,plain,(
    ! [B_156,C_157] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_156,C_157),C_157)
      | k1_xboole_0 = C_157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1959,c_1418,c_1418,c_672])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [D_75,A_76,B_77] :
      ( ~ r2_hidden(D_75,'#skF_2'(A_76,B_77))
      | ~ r2_hidden(D_75,B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2138,plain,(
    ! [A_308,B_309,B_310] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_308,B_309),B_310),B_309)
      | ~ r2_hidden(A_308,B_309)
      | r1_xboole_0('#skF_2'(A_308,B_309),B_310) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_2144,plain,(
    ! [A_311,B_312] :
      ( ~ r2_hidden(A_311,B_312)
      | r1_xboole_0('#skF_2'(A_311,B_312),B_312) ) ),
    inference(resolution,[status(thm)],[c_4,c_2138])).

tff(c_91,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    ! [B_52] :
      ( ~ r1_xboole_0(B_52,'#skF_9')
      | ~ r2_hidden(B_52,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_100,plain,(
    ! [A_63] :
      ( ~ r1_xboole_0('#skF_2'(A_63,'#skF_9'),'#skF_9')
      | ~ r2_hidden(A_63,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_91,c_44])).

tff(c_2153,plain,(
    ! [A_313] : ~ r2_hidden(A_313,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2144,c_100])).

tff(c_2157,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2096,c_2153])).

tff(c_2217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.58  
% 3.58/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k3_setfam_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.58/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.58/1.59  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.58/1.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.58/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.58/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.58/1.59  tff(k3_setfam_1, type, k3_setfam_1: ($i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.58/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.59  
% 3.58/1.60  tff(f_88, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.58/1.60  tff(f_77, axiom, (![A, B, C]: ((C = k3_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k3_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_setfam_1)).
% 3.58/1.60  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.58/1.60  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.58/1.60  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.58/1.60  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.58/1.60  tff(c_46, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.58/1.60  tff(c_573, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_4'(A_155, B_156, C_157), A_155) | r2_hidden('#skF_6'(A_155, B_156, C_157), C_157) | k3_setfam_1(A_155, B_156)=C_157)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.58/1.60  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.60  tff(c_69, plain, (![A_55, B_56]: (~r2_hidden(A_55, k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.58/1.60  tff(c_72, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 3.58/1.60  tff(c_1929, plain, (![A_276, B_277]: (r2_hidden('#skF_4'(A_276, B_277, k1_xboole_0), A_276) | k3_setfam_1(A_276, B_277)=k1_xboole_0)), inference(resolution, [status(thm)], [c_573, c_72])).
% 3.58/1.60  tff(c_1959, plain, (![B_277]: (k3_setfam_1(k1_xboole_0, B_277)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1929, c_72])).
% 3.58/1.60  tff(c_931, plain, (![A_192, B_193, C_194]: (r2_hidden('#skF_5'(A_192, B_193, C_194), B_193) | r2_hidden('#skF_6'(A_192, B_193, C_194), C_194) | k3_setfam_1(A_192, B_193)=C_194)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.58/1.60  tff(c_1333, plain, (![A_255, B_256]: (r2_hidden('#skF_5'(A_255, B_256, k1_xboole_0), B_256) | k3_setfam_1(A_255, B_256)=k1_xboole_0)), inference(resolution, [status(thm)], [c_931, c_72])).
% 3.58/1.60  tff(c_1418, plain, (![A_255]: (k3_setfam_1(A_255, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1333, c_72])).
% 3.58/1.60  tff(c_231, plain, (![A_97, B_98, D_99]: (r2_hidden('#skF_8'(A_97, B_98, k3_setfam_1(A_97, B_98), D_99), B_98) | ~r2_hidden(D_99, k3_setfam_1(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.58/1.60  tff(c_256, plain, (![D_99, A_97]: (~r2_hidden(D_99, k3_setfam_1(A_97, k1_xboole_0)))), inference(resolution, [status(thm)], [c_231, c_72])).
% 3.58/1.60  tff(c_672, plain, (![A_97, B_156, C_157]: (r2_hidden('#skF_6'(k3_setfam_1(A_97, k1_xboole_0), B_156, C_157), C_157) | k3_setfam_1(k3_setfam_1(A_97, k1_xboole_0), B_156)=C_157)), inference(resolution, [status(thm)], [c_573, c_256])).
% 3.58/1.60  tff(c_2096, plain, (![B_156, C_157]: (r2_hidden('#skF_6'(k1_xboole_0, B_156, C_157), C_157) | k1_xboole_0=C_157)), inference(demodulation, [status(thm), theory('equality')], [c_1959, c_1418, c_1418, c_672])).
% 3.58/1.60  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.60  tff(c_134, plain, (![D_75, A_76, B_77]: (~r2_hidden(D_75, '#skF_2'(A_76, B_77)) | ~r2_hidden(D_75, B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.60  tff(c_2138, plain, (![A_308, B_309, B_310]: (~r2_hidden('#skF_1'('#skF_2'(A_308, B_309), B_310), B_309) | ~r2_hidden(A_308, B_309) | r1_xboole_0('#skF_2'(A_308, B_309), B_310))), inference(resolution, [status(thm)], [c_6, c_134])).
% 3.58/1.60  tff(c_2144, plain, (![A_311, B_312]: (~r2_hidden(A_311, B_312) | r1_xboole_0('#skF_2'(A_311, B_312), B_312))), inference(resolution, [status(thm)], [c_4, c_2138])).
% 3.58/1.60  tff(c_91, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.60  tff(c_44, plain, (![B_52]: (~r1_xboole_0(B_52, '#skF_9') | ~r2_hidden(B_52, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.58/1.60  tff(c_100, plain, (![A_63]: (~r1_xboole_0('#skF_2'(A_63, '#skF_9'), '#skF_9') | ~r2_hidden(A_63, '#skF_9'))), inference(resolution, [status(thm)], [c_91, c_44])).
% 3.58/1.60  tff(c_2153, plain, (![A_313]: (~r2_hidden(A_313, '#skF_9'))), inference(resolution, [status(thm)], [c_2144, c_100])).
% 3.58/1.60  tff(c_2157, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2096, c_2153])).
% 3.58/1.60  tff(c_2217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2157])).
% 3.58/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.60  
% 3.58/1.60  Inference rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Ref     : 0
% 3.58/1.60  #Sup     : 438
% 3.58/1.60  #Fact    : 0
% 3.58/1.60  #Define  : 0
% 3.58/1.60  #Split   : 0
% 3.58/1.60  #Chain   : 0
% 3.58/1.60  #Close   : 0
% 3.58/1.60  
% 3.58/1.60  Ordering : KBO
% 3.58/1.60  
% 3.58/1.60  Simplification rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Subsume      : 172
% 3.58/1.60  #Demod        : 360
% 3.58/1.60  #Tautology    : 133
% 3.58/1.60  #SimpNegUnit  : 17
% 3.58/1.60  #BackRed      : 46
% 3.58/1.60  
% 3.58/1.60  #Partial instantiations: 0
% 3.58/1.60  #Strategies tried      : 1
% 3.58/1.60  
% 3.58/1.60  Timing (in seconds)
% 3.58/1.60  ----------------------
% 3.58/1.60  Preprocessing        : 0.30
% 3.58/1.60  Parsing              : 0.15
% 3.58/1.60  CNF conversion       : 0.03
% 3.58/1.60  Main loop            : 0.55
% 3.58/1.60  Inferencing          : 0.20
% 3.58/1.60  Reduction            : 0.17
% 3.58/1.60  Demodulation         : 0.12
% 3.58/1.60  BG Simplification    : 0.03
% 3.58/1.60  Subsumption          : 0.11
% 3.58/1.60  Abstraction          : 0.03
% 3.58/1.60  MUC search           : 0.00
% 3.58/1.60  Cooper               : 0.00
% 3.58/1.60  Total                : 0.87
% 3.58/1.60  Index Insertion      : 0.00
% 3.58/1.60  Index Deletion       : 0.00
% 3.58/1.60  Index Matching       : 0.00
% 3.58/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
