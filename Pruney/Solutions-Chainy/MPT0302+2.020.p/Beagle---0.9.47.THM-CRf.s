%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 117 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 221 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_68,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_381,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( r2_hidden(k4_tarski(A_125,B_126),k2_zfmisc_1(C_127,D_128))
      | ~ r2_hidden(B_126,D_128)
      | ~ r2_hidden(A_125,C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_10','#skF_9') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_160,plain,(
    ! [B_77,D_78,A_79,C_80] :
      ( r2_hidden(B_77,D_78)
      | ~ r2_hidden(k4_tarski(A_79,B_77),k2_zfmisc_1(C_80,D_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_163,plain,(
    ! [B_77,A_79] :
      ( r2_hidden(B_77,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_79,B_77),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_160])).

tff(c_409,plain,(
    ! [B_126,A_125] :
      ( r2_hidden(B_126,'#skF_9')
      | ~ r2_hidden(B_126,'#skF_10')
      | ~ r2_hidden(A_125,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_381,c_163])).

tff(c_424,plain,(
    ! [A_131] : ~ r2_hidden(A_131,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_446,plain,(
    ! [B_133] : r1_tarski('#skF_9',B_133) ),
    inference(resolution,[status(thm)],[c_6,c_424])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_12)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_199,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(A_100,B_101)
      | ~ r2_hidden(A_100,C_102)
      | r2_hidden(A_100,k5_xboole_0(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_220,plain,(
    ! [A_103,A_104] :
      ( r2_hidden(A_103,A_104)
      | ~ r2_hidden(A_103,k1_xboole_0)
      | r2_hidden(A_103,A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_199])).

tff(c_247,plain,(
    ! [A_108,A_109] :
      ( r2_hidden('#skF_2'(A_108,k1_xboole_0),A_109)
      | ~ r2_xboole_0(A_108,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_220])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),A_11)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,(
    ! [A_110] : ~ r2_xboole_0(A_110,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_247,c_26])).

tff(c_275,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_270])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_446,c_275])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_452])).

tff(c_495,plain,(
    ! [B_137] :
      ( r2_hidden(B_137,'#skF_9')
      | ~ r2_hidden(B_137,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_531,plain,(
    ! [B_139] :
      ( r2_hidden('#skF_1'('#skF_10',B_139),'#skF_9')
      | r1_tarski('#skF_10',B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_495])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_539,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_531,c_4])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_173,plain,(
    ! [A_88,C_89,B_90,D_91] :
      ( r2_hidden(A_88,C_89)
      | ~ r2_hidden(k4_tarski(A_88,B_90),k2_zfmisc_1(C_89,D_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_176,plain,(
    ! [A_88,B_90] :
      ( r2_hidden(A_88,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_88,B_90),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_173])).

tff(c_407,plain,(
    ! [A_125,B_126] :
      ( r2_hidden(A_125,'#skF_10')
      | ~ r2_hidden(B_126,'#skF_10')
      | ~ r2_hidden(A_125,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_381,c_176])).

tff(c_546,plain,(
    ! [B_140] : ~ r2_hidden(B_140,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_617,plain,(
    ! [B_145] : r1_tarski('#skF_10',B_145) ),
    inference(resolution,[status(thm)],[c_6,c_546])).

tff(c_623,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_617,c_275])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_623])).

tff(c_630,plain,(
    ! [A_146] :
      ( r2_hidden(A_146,'#skF_10')
      | ~ r2_hidden(A_146,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_648,plain,(
    ! [B_147] :
      ( ~ r2_xboole_0('#skF_10',B_147)
      | ~ r2_hidden('#skF_2'('#skF_10',B_147),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_630,c_26])).

tff(c_663,plain,(
    ~ r2_xboole_0('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_648])).

tff(c_686,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_663])).

tff(c_689,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_686])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:08:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.39  %$ r2_xboole_0 > r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1
% 2.73/1.39  
% 2.73/1.39  %Foreground sorts:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Background operators:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Foreground operators:
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.73/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.73/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.73/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.73/1.39  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.73/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.73/1.39  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.73/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.39  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.39  
% 2.73/1.40  tff(f_91, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.73/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.73/1.40  tff(f_76, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.73/1.40  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.73/1.40  tff(f_56, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.73/1.40  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.73/1.40  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.73/1.40  tff(c_68, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.40  tff(c_72, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.40  tff(c_381, plain, (![A_125, B_126, C_127, D_128]: (r2_hidden(k4_tarski(A_125, B_126), k2_zfmisc_1(C_127, D_128)) | ~r2_hidden(B_126, D_128) | ~r2_hidden(A_125, C_127))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.40  tff(c_74, plain, (k2_zfmisc_1('#skF_10', '#skF_9')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.40  tff(c_160, plain, (![B_77, D_78, A_79, C_80]: (r2_hidden(B_77, D_78) | ~r2_hidden(k4_tarski(A_79, B_77), k2_zfmisc_1(C_80, D_78)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.40  tff(c_163, plain, (![B_77, A_79]: (r2_hidden(B_77, '#skF_9') | ~r2_hidden(k4_tarski(A_79, B_77), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_160])).
% 2.73/1.40  tff(c_409, plain, (![B_126, A_125]: (r2_hidden(B_126, '#skF_9') | ~r2_hidden(B_126, '#skF_10') | ~r2_hidden(A_125, '#skF_9'))), inference(resolution, [status(thm)], [c_381, c_163])).
% 2.73/1.40  tff(c_424, plain, (![A_131]: (~r2_hidden(A_131, '#skF_9'))), inference(splitLeft, [status(thm)], [c_409])).
% 2.73/1.40  tff(c_446, plain, (![B_133]: (r1_tarski('#skF_9', B_133))), inference(resolution, [status(thm)], [c_6, c_424])).
% 2.73/1.40  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.40  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), B_12) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.40  tff(c_30, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.40  tff(c_199, plain, (![A_100, B_101, C_102]: (r2_hidden(A_100, B_101) | ~r2_hidden(A_100, C_102) | r2_hidden(A_100, k5_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.73/1.40  tff(c_220, plain, (![A_103, A_104]: (r2_hidden(A_103, A_104) | ~r2_hidden(A_103, k1_xboole_0) | r2_hidden(A_103, A_104))), inference(superposition, [status(thm), theory('equality')], [c_30, c_199])).
% 2.73/1.40  tff(c_247, plain, (![A_108, A_109]: (r2_hidden('#skF_2'(A_108, k1_xboole_0), A_109) | ~r2_xboole_0(A_108, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_220])).
% 2.73/1.40  tff(c_26, plain, (![A_11, B_12]: (~r2_hidden('#skF_2'(A_11, B_12), A_11) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.40  tff(c_270, plain, (![A_110]: (~r2_xboole_0(A_110, k1_xboole_0))), inference(resolution, [status(thm)], [c_247, c_26])).
% 2.73/1.40  tff(c_275, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_270])).
% 2.73/1.40  tff(c_452, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_446, c_275])).
% 2.73/1.40  tff(c_457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_452])).
% 2.73/1.40  tff(c_495, plain, (![B_137]: (r2_hidden(B_137, '#skF_9') | ~r2_hidden(B_137, '#skF_10'))), inference(splitRight, [status(thm)], [c_409])).
% 2.73/1.40  tff(c_531, plain, (![B_139]: (r2_hidden('#skF_1'('#skF_10', B_139), '#skF_9') | r1_tarski('#skF_10', B_139))), inference(resolution, [status(thm)], [c_6, c_495])).
% 2.73/1.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.40  tff(c_539, plain, (r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_531, c_4])).
% 2.73/1.40  tff(c_70, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.40  tff(c_173, plain, (![A_88, C_89, B_90, D_91]: (r2_hidden(A_88, C_89) | ~r2_hidden(k4_tarski(A_88, B_90), k2_zfmisc_1(C_89, D_91)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.40  tff(c_176, plain, (![A_88, B_90]: (r2_hidden(A_88, '#skF_10') | ~r2_hidden(k4_tarski(A_88, B_90), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_173])).
% 2.73/1.40  tff(c_407, plain, (![A_125, B_126]: (r2_hidden(A_125, '#skF_10') | ~r2_hidden(B_126, '#skF_10') | ~r2_hidden(A_125, '#skF_9'))), inference(resolution, [status(thm)], [c_381, c_176])).
% 2.73/1.40  tff(c_546, plain, (![B_140]: (~r2_hidden(B_140, '#skF_10'))), inference(splitLeft, [status(thm)], [c_407])).
% 2.73/1.40  tff(c_617, plain, (![B_145]: (r1_tarski('#skF_10', B_145))), inference(resolution, [status(thm)], [c_6, c_546])).
% 2.73/1.40  tff(c_623, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_617, c_275])).
% 2.73/1.40  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_623])).
% 2.73/1.40  tff(c_630, plain, (![A_146]: (r2_hidden(A_146, '#skF_10') | ~r2_hidden(A_146, '#skF_9'))), inference(splitRight, [status(thm)], [c_407])).
% 2.73/1.40  tff(c_648, plain, (![B_147]: (~r2_xboole_0('#skF_10', B_147) | ~r2_hidden('#skF_2'('#skF_10', B_147), '#skF_9'))), inference(resolution, [status(thm)], [c_630, c_26])).
% 2.73/1.40  tff(c_663, plain, (~r2_xboole_0('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_28, c_648])).
% 2.73/1.40  tff(c_686, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_8, c_663])).
% 2.73/1.40  tff(c_689, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_539, c_686])).
% 2.73/1.40  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_689])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 130
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 2
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 20
% 2.73/1.40  #Demod        : 20
% 2.73/1.40  #Tautology    : 34
% 2.73/1.40  #SimpNegUnit  : 9
% 2.73/1.40  #BackRed      : 2
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.33
% 2.73/1.40  Parsing              : 0.17
% 2.73/1.40  CNF conversion       : 0.03
% 2.73/1.40  Main loop            : 0.30
% 2.73/1.40  Inferencing          : 0.11
% 2.73/1.40  Reduction            : 0.08
% 2.73/1.40  Demodulation         : 0.05
% 2.73/1.40  BG Simplification    : 0.02
% 2.73/1.40  Subsumption          : 0.07
% 2.73/1.40  Abstraction          : 0.01
% 2.73/1.40  MUC search           : 0.00
% 2.73/1.40  Cooper               : 0.00
% 2.73/1.40  Total                : 0.66
% 2.73/1.41  Index Insertion      : 0.00
% 2.73/1.41  Index Deletion       : 0.00
% 2.73/1.41  Index Matching       : 0.00
% 2.73/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
