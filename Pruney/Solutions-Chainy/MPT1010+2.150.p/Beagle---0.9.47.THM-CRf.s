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
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 122 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_90,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden(A_63,B_64)
      | k4_xboole_0(k1_tarski(A_63),B_64) != k1_tarski(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_147,plain,(
    ! [A_63] : ~ r2_hidden(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_98,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_96,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_94,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_92,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_341,plain,(
    ! [D_175,C_176,B_177,A_178] :
      ( r2_hidden(k1_funct_1(D_175,C_176),B_177)
      | k1_xboole_0 = B_177
      | ~ r2_hidden(C_176,A_178)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177)))
      | ~ v1_funct_2(D_175,A_178,B_177)
      | ~ v1_funct_1(D_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_492,plain,(
    ! [D_226,B_227] :
      ( r2_hidden(k1_funct_1(D_226,'#skF_7'),B_227)
      | k1_xboole_0 = B_227
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_227)))
      | ~ v1_funct_2(D_226,'#skF_5',B_227)
      | ~ v1_funct_1(D_226) ) ),
    inference(resolution,[status(thm)],[c_92,c_341])).

tff(c_495,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_492])).

tff(c_498,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_495])).

tff(c_514,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_538,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_6])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_538])).

tff(c_548,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_555,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_548,c_4])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  
% 3.38/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 3.38/1.51  
% 3.38/1.51  %Foreground sorts:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Background operators:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Foreground operators:
% 3.38/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.51  
% 3.38/1.52  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.38/1.52  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.38/1.52  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.38/1.52  tff(f_95, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.38/1.52  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.38/1.52  tff(c_90, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.52  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.52  tff(c_142, plain, (![A_63, B_64]: (~r2_hidden(A_63, B_64) | k4_xboole_0(k1_tarski(A_63), B_64)!=k1_tarski(A_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.52  tff(c_147, plain, (![A_63]: (~r2_hidden(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_142])).
% 3.38/1.52  tff(c_98, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.52  tff(c_96, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.52  tff(c_94, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.52  tff(c_92, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.52  tff(c_341, plain, (![D_175, C_176, B_177, A_178]: (r2_hidden(k1_funct_1(D_175, C_176), B_177) | k1_xboole_0=B_177 | ~r2_hidden(C_176, A_178) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))) | ~v1_funct_2(D_175, A_178, B_177) | ~v1_funct_1(D_175))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.38/1.52  tff(c_492, plain, (![D_226, B_227]: (r2_hidden(k1_funct_1(D_226, '#skF_7'), B_227) | k1_xboole_0=B_227 | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_227))) | ~v1_funct_2(D_226, '#skF_5', B_227) | ~v1_funct_1(D_226))), inference(resolution, [status(thm)], [c_92, c_341])).
% 3.38/1.52  tff(c_495, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_94, c_492])).
% 3.38/1.52  tff(c_498, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_495])).
% 3.38/1.52  tff(c_514, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_498])).
% 3.38/1.52  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.38/1.52  tff(c_538, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_514, c_6])).
% 3.38/1.52  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_538])).
% 3.38/1.52  tff(c_548, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_498])).
% 3.38/1.52  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.38/1.52  tff(c_555, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_548, c_4])).
% 3.38/1.52  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_555])).
% 3.38/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.52  
% 3.38/1.52  Inference rules
% 3.38/1.52  ----------------------
% 3.38/1.52  #Ref     : 0
% 3.38/1.52  #Sup     : 108
% 3.38/1.52  #Fact    : 0
% 3.38/1.52  #Define  : 0
% 3.38/1.52  #Split   : 1
% 3.38/1.52  #Chain   : 0
% 3.38/1.52  #Close   : 0
% 3.38/1.52  
% 3.38/1.52  Ordering : KBO
% 3.38/1.52  
% 3.38/1.52  Simplification rules
% 3.38/1.52  ----------------------
% 3.38/1.52  #Subsume      : 6
% 3.38/1.52  #Demod        : 27
% 3.38/1.52  #Tautology    : 48
% 3.38/1.52  #SimpNegUnit  : 5
% 3.38/1.52  #BackRed      : 2
% 3.38/1.52  
% 3.38/1.52  #Partial instantiations: 0
% 3.38/1.52  #Strategies tried      : 1
% 3.38/1.52  
% 3.38/1.52  Timing (in seconds)
% 3.38/1.52  ----------------------
% 3.38/1.53  Preprocessing        : 0.35
% 3.38/1.53  Parsing              : 0.16
% 3.38/1.53  CNF conversion       : 0.03
% 3.38/1.53  Main loop            : 0.35
% 3.38/1.53  Inferencing          : 0.10
% 3.38/1.53  Reduction            : 0.10
% 3.38/1.53  Demodulation         : 0.07
% 3.38/1.53  BG Simplification    : 0.03
% 3.38/1.53  Subsumption          : 0.11
% 3.38/1.53  Abstraction          : 0.03
% 3.38/1.53  MUC search           : 0.00
% 3.38/1.53  Cooper               : 0.00
% 3.38/1.53  Total                : 0.72
% 3.38/1.53  Index Insertion      : 0.00
% 3.38/1.53  Index Deletion       : 0.00
% 3.38/1.53  Index Matching       : 0.00
% 3.38/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
