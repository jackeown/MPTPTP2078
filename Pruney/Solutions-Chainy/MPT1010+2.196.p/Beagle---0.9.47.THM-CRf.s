%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  83 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    ! [A_27,B_28] : k4_xboole_0(k1_tarski(A_27),k2_tarski(A_27,B_28)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_26,plain,(
    ! [B_14] : k4_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_tarski(B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_26])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2280,plain,(
    ! [D_2734,C_2735,B_2736,A_2737] :
      ( r2_hidden(k1_funct_1(D_2734,C_2735),B_2736)
      | k1_xboole_0 = B_2736
      | ~ r2_hidden(C_2735,A_2737)
      | ~ m1_subset_1(D_2734,k1_zfmisc_1(k2_zfmisc_1(A_2737,B_2736)))
      | ~ v1_funct_2(D_2734,A_2737,B_2736)
      | ~ v1_funct_1(D_2734) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4628,plain,(
    ! [D_4004,B_4005] :
      ( r2_hidden(k1_funct_1(D_4004,'#skF_5'),B_4005)
      | k1_xboole_0 = B_4005
      | ~ m1_subset_1(D_4004,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_4005)))
      | ~ v1_funct_2(D_4004,'#skF_3',B_4005)
      | ~ v1_funct_1(D_4004) ) ),
    inference(resolution,[status(thm)],[c_36,c_2280])).

tff(c_4637,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_4628])).

tff(c_4640,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4637])).

tff(c_4641,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4640])).

tff(c_120,plain,(
    ! [D_38,B_39,A_40] :
      ( D_38 = B_39
      | D_38 = A_40
      | ~ r2_hidden(D_38,k2_tarski(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [D_38,A_7] :
      ( D_38 = A_7
      | D_38 = A_7
      | ~ r2_hidden(D_38,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_120])).

tff(c_4646,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4641,c_123])).

tff(c_4691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_4646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.94  
% 4.79/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.94  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.79/1.94  
% 4.79/1.94  %Foreground sorts:
% 4.79/1.94  
% 4.79/1.94  
% 4.79/1.94  %Background operators:
% 4.79/1.94  
% 4.79/1.94  
% 4.79/1.94  %Foreground operators:
% 4.79/1.94  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.79/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.79/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.79/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.79/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.79/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.79/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.79/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.79/1.94  tff('#skF_6', type, '#skF_6': $i).
% 4.79/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.79/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.79/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.79/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.79/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.94  
% 4.79/1.95  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.79/1.95  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.79/1.95  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 4.79/1.95  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.79/1.95  tff(f_59, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.79/1.95  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.79/1.95  tff(c_34, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.95  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.79/1.95  tff(c_62, plain, (![A_27, B_28]: (k4_xboole_0(k1_tarski(A_27), k2_tarski(A_27, B_28))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.79/1.95  tff(c_69, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_62])).
% 4.79/1.95  tff(c_26, plain, (![B_14]: (k4_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_tarski(B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.79/1.95  tff(c_88, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_26])).
% 4.79/1.95  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.95  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.95  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.95  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.95  tff(c_2280, plain, (![D_2734, C_2735, B_2736, A_2737]: (r2_hidden(k1_funct_1(D_2734, C_2735), B_2736) | k1_xboole_0=B_2736 | ~r2_hidden(C_2735, A_2737) | ~m1_subset_1(D_2734, k1_zfmisc_1(k2_zfmisc_1(A_2737, B_2736))) | ~v1_funct_2(D_2734, A_2737, B_2736) | ~v1_funct_1(D_2734))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.79/1.95  tff(c_4628, plain, (![D_4004, B_4005]: (r2_hidden(k1_funct_1(D_4004, '#skF_5'), B_4005) | k1_xboole_0=B_4005 | ~m1_subset_1(D_4004, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_4005))) | ~v1_funct_2(D_4004, '#skF_3', B_4005) | ~v1_funct_1(D_4004))), inference(resolution, [status(thm)], [c_36, c_2280])).
% 4.79/1.95  tff(c_4637, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_4628])).
% 4.79/1.95  tff(c_4640, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4637])).
% 4.79/1.95  tff(c_4641, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_88, c_4640])).
% 4.79/1.95  tff(c_120, plain, (![D_38, B_39, A_40]: (D_38=B_39 | D_38=A_40 | ~r2_hidden(D_38, k2_tarski(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.79/1.95  tff(c_123, plain, (![D_38, A_7]: (D_38=A_7 | D_38=A_7 | ~r2_hidden(D_38, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_120])).
% 4.79/1.95  tff(c_4646, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4641, c_123])).
% 4.79/1.95  tff(c_4691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_4646])).
% 4.79/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.95  
% 4.79/1.95  Inference rules
% 4.79/1.95  ----------------------
% 4.79/1.95  #Ref     : 0
% 4.79/1.95  #Sup     : 647
% 4.79/1.95  #Fact    : 12
% 4.79/1.95  #Define  : 0
% 4.79/1.95  #Split   : 5
% 4.79/1.95  #Chain   : 0
% 4.79/1.95  #Close   : 0
% 4.79/1.95  
% 4.79/1.95  Ordering : KBO
% 4.79/1.95  
% 4.79/1.95  Simplification rules
% 4.79/1.95  ----------------------
% 4.79/1.95  #Subsume      : 115
% 4.79/1.95  #Demod        : 76
% 4.79/1.95  #Tautology    : 258
% 4.79/1.95  #SimpNegUnit  : 18
% 4.79/1.95  #BackRed      : 0
% 4.79/1.95  
% 4.79/1.95  #Partial instantiations: 2610
% 4.79/1.95  #Strategies tried      : 1
% 4.79/1.95  
% 4.79/1.95  Timing (in seconds)
% 4.79/1.95  ----------------------
% 4.79/1.95  Preprocessing        : 0.32
% 4.79/1.95  Parsing              : 0.16
% 4.79/1.95  CNF conversion       : 0.02
% 4.79/1.95  Main loop            : 0.87
% 4.79/1.95  Inferencing          : 0.46
% 4.79/1.95  Reduction            : 0.20
% 4.79/1.95  Demodulation         : 0.14
% 4.79/1.95  BG Simplification    : 0.05
% 4.79/1.96  Subsumption          : 0.12
% 4.79/1.96  Abstraction          : 0.05
% 4.79/1.96  MUC search           : 0.00
% 4.79/1.96  Cooper               : 0.00
% 4.79/1.96  Total                : 1.22
% 4.79/1.96  Index Insertion      : 0.00
% 4.79/1.96  Index Deletion       : 0.00
% 4.79/1.96  Index Matching       : 0.00
% 4.79/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
