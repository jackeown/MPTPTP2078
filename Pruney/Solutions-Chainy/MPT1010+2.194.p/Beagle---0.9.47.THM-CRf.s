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
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 139 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_36,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [A_27,B_28] : ~ r2_hidden(A_27,k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [A_13] : ~ r2_hidden(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1932,plain,(
    ! [D_2506,C_2507,B_2508,A_2509] :
      ( r2_hidden(k1_funct_1(D_2506,C_2507),B_2508)
      | k1_xboole_0 = B_2508
      | ~ r2_hidden(C_2507,A_2509)
      | ~ m1_subset_1(D_2506,k1_zfmisc_1(k2_zfmisc_1(A_2509,B_2508)))
      | ~ v1_funct_2(D_2506,A_2509,B_2508)
      | ~ v1_funct_1(D_2506) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2738,plain,(
    ! [D_3030,B_3031] :
      ( r2_hidden(k1_funct_1(D_3030,'#skF_5'),B_3031)
      | k1_xboole_0 = B_3031
      | ~ m1_subset_1(D_3030,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_3031)))
      | ~ v1_funct_2(D_3030,'#skF_3',B_3031)
      | ~ v1_funct_1(D_3030) ) ),
    inference(resolution,[status(thm)],[c_38,c_1932])).

tff(c_2747,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_2738])).

tff(c_2754,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2747])).

tff(c_2757,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2754])).

tff(c_68,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_2773,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2757,c_74])).

tff(c_2816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2773])).

tff(c_2817,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2754])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_123,plain,(
    ! [D_39,B_40,A_41] :
      ( D_39 = B_40
      | D_39 = A_41
      | ~ r2_hidden(D_39,k2_tarski(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_129,plain,(
    ! [D_39,A_7] :
      ( D_39 = A_7
      | D_39 = A_7
      | ~ r2_hidden(D_39,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_2829,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2817,c_129])).

tff(c_2874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_2829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.70  
% 3.72/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.70  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.72/1.70  
% 3.72/1.70  %Foreground sorts:
% 3.72/1.70  
% 3.72/1.70  
% 3.72/1.70  %Background operators:
% 3.72/1.70  
% 3.72/1.70  
% 3.72/1.70  %Foreground operators:
% 3.72/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.72/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.72/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.72/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.72/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.72/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.72/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.70  
% 3.72/1.71  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.72/1.71  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.72/1.71  tff(f_49, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.72/1.71  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.72/1.71  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.72/1.71  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.72/1.71  tff(c_36, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.72/1.71  tff(c_28, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.72/1.71  tff(c_81, plain, (![A_27, B_28]: (~r2_hidden(A_27, k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.71  tff(c_84, plain, (![A_13]: (~r2_hidden(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_81])).
% 3.72/1.71  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.72/1.71  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.72/1.71  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.72/1.71  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.72/1.71  tff(c_1932, plain, (![D_2506, C_2507, B_2508, A_2509]: (r2_hidden(k1_funct_1(D_2506, C_2507), B_2508) | k1_xboole_0=B_2508 | ~r2_hidden(C_2507, A_2509) | ~m1_subset_1(D_2506, k1_zfmisc_1(k2_zfmisc_1(A_2509, B_2508))) | ~v1_funct_2(D_2506, A_2509, B_2508) | ~v1_funct_1(D_2506))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.72/1.71  tff(c_2738, plain, (![D_3030, B_3031]: (r2_hidden(k1_funct_1(D_3030, '#skF_5'), B_3031) | k1_xboole_0=B_3031 | ~m1_subset_1(D_3030, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_3031))) | ~v1_funct_2(D_3030, '#skF_3', B_3031) | ~v1_funct_1(D_3030))), inference(resolution, [status(thm)], [c_38, c_1932])).
% 3.72/1.71  tff(c_2747, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_2738])).
% 3.72/1.71  tff(c_2754, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2747])).
% 3.72/1.71  tff(c_2757, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2754])).
% 3.72/1.71  tff(c_68, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.72/1.71  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.72/1.71  tff(c_74, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 3.72/1.71  tff(c_2773, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2757, c_74])).
% 3.72/1.71  tff(c_2816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2773])).
% 3.72/1.71  tff(c_2817, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_2754])).
% 3.72/1.71  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.72/1.71  tff(c_123, plain, (![D_39, B_40, A_41]: (D_39=B_40 | D_39=A_41 | ~r2_hidden(D_39, k2_tarski(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.72/1.71  tff(c_129, plain, (![D_39, A_7]: (D_39=A_7 | D_39=A_7 | ~r2_hidden(D_39, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_123])).
% 3.72/1.71  tff(c_2829, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2817, c_129])).
% 3.72/1.71  tff(c_2874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_2829])).
% 3.72/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.71  
% 3.72/1.71  Inference rules
% 3.72/1.71  ----------------------
% 3.72/1.71  #Ref     : 0
% 3.72/1.71  #Sup     : 400
% 3.72/1.71  #Fact    : 10
% 3.72/1.71  #Define  : 0
% 3.72/1.71  #Split   : 5
% 3.72/1.71  #Chain   : 0
% 3.72/1.71  #Close   : 0
% 3.72/1.71  
% 3.72/1.71  Ordering : KBO
% 3.72/1.71  
% 3.72/1.71  Simplification rules
% 3.72/1.71  ----------------------
% 3.72/1.71  #Subsume      : 100
% 3.72/1.71  #Demod        : 78
% 3.72/1.71  #Tautology    : 120
% 3.72/1.71  #SimpNegUnit  : 14
% 3.72/1.71  #BackRed      : 2
% 3.72/1.71  
% 3.72/1.71  #Partial instantiations: 2100
% 3.72/1.71  #Strategies tried      : 1
% 3.72/1.71  
% 3.72/1.71  Timing (in seconds)
% 3.72/1.71  ----------------------
% 3.72/1.71  Preprocessing        : 0.30
% 3.72/1.71  Parsing              : 0.15
% 3.72/1.71  CNF conversion       : 0.02
% 3.72/1.71  Main loop            : 0.61
% 3.72/1.71  Inferencing          : 0.31
% 3.72/1.71  Reduction            : 0.14
% 3.72/1.71  Demodulation         : 0.10
% 3.72/1.71  BG Simplification    : 0.03
% 3.72/1.71  Subsumption          : 0.09
% 3.72/1.71  Abstraction          : 0.04
% 3.72/1.71  MUC search           : 0.00
% 3.72/1.71  Cooper               : 0.00
% 3.72/1.71  Total                : 0.93
% 3.72/1.71  Index Insertion      : 0.00
% 3.72/1.71  Index Deletion       : 0.00
% 3.72/1.71  Index Matching       : 0.00
% 3.72/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
