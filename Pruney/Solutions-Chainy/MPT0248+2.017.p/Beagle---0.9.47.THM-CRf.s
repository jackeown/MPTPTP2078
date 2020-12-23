%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:06 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 144 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 345 expanded)
%              Number of equality atoms :   84 ( 326 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_59])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_418,plain,(
    ! [B_46,C_47,A_48] :
      ( k2_tarski(B_46,C_47) = A_48
      | k1_tarski(C_47) = A_48
      | k1_tarski(B_46) = A_48
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,k2_tarski(B_46,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_444,plain,(
    ! [A_8,A_48] :
      ( k2_tarski(A_8,A_8) = A_48
      | k1_tarski(A_8) = A_48
      | k1_tarski(A_8) = A_48
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_418])).

tff(c_597,plain,(
    ! [A_55,A_56] :
      ( k1_tarski(A_55) = A_56
      | k1_tarski(A_55) = A_56
      | k1_tarski(A_55) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_tarski(A_55)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_444])).

tff(c_611,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_597])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_40,c_40,c_40,c_611])).

tff(c_621,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_622,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_623,plain,(
    ! [A_1] : k4_xboole_0(A_1,'#skF_2') = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_2])).

tff(c_815,plain,(
    ! [A_79,B_80] : k4_xboole_0(k2_xboole_0(A_79,B_80),B_80) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_822,plain,(
    ! [A_79] : k4_xboole_0(A_79,'#skF_2') = k2_xboole_0(A_79,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_623])).

tff(c_837,plain,(
    ! [A_79] : k2_xboole_0(A_79,'#skF_2') = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_822])).

tff(c_8,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_724,plain,(
    ! [A_71,B_72] : k3_tarski(k2_tarski(A_71,B_72)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_789,plain,(
    ! [B_77,A_78] : k3_tarski(k2_tarski(B_77,A_78)) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_724])).

tff(c_22,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_864,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_22])).

tff(c_893,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_30])).

tff(c_931,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_893])).

tff(c_933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_931])).

tff(c_934,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_935,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_989,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_935,c_28])).

tff(c_957,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_30])).

tff(c_1100,plain,(
    ! [A_102,B_103] : k3_tarski(k2_tarski(A_102,B_103)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1239,plain,(
    ! [B_112,A_113] : k3_tarski(k2_tarski(B_112,A_113)) = k2_xboole_0(A_113,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1100])).

tff(c_1313,plain,(
    ! [B_117,A_118] : k2_xboole_0(B_117,A_118) = k2_xboole_0(A_118,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_22])).

tff(c_1375,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_1313])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1443,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_6])).

tff(c_1265,plain,(
    ! [B_114,C_115,A_116] :
      ( k2_tarski(B_114,C_115) = A_116
      | k1_tarski(C_115) = A_116
      | k1_tarski(B_114) = A_116
      | k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,k2_tarski(B_114,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1293,plain,(
    ! [A_8,A_116] :
      ( k2_tarski(A_8,A_8) = A_116
      | k1_tarski(A_8) = A_116
      | k1_tarski(A_8) = A_116
      | k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1265])).

tff(c_1596,plain,(
    ! [A_127,A_128] :
      ( k1_tarski(A_127) = A_128
      | k1_tarski(A_127) = A_128
      | k1_tarski(A_127) = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,k1_tarski(A_127)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1293])).

tff(c_1607,plain,(
    ! [A_128] :
      ( k1_tarski('#skF_1') = A_128
      | k1_tarski('#skF_1') = A_128
      | k1_tarski('#skF_1') = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_1596])).

tff(c_1614,plain,(
    ! [A_129] :
      ( A_129 = '#skF_2'
      | A_129 = '#skF_2'
      | A_129 = '#skF_2'
      | k1_xboole_0 = A_129
      | ~ r1_tarski(A_129,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_935,c_935,c_1607])).

tff(c_1617,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1443,c_1614])).

tff(c_1629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_989,c_989,c_989,c_1617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.58  
% 3.06/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.58  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.58  
% 3.06/1.58  %Foreground sorts:
% 3.06/1.58  
% 3.06/1.58  
% 3.06/1.58  %Background operators:
% 3.06/1.58  
% 3.06/1.58  
% 3.06/1.58  %Foreground operators:
% 3.06/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.06/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.58  
% 3.06/1.59  tff(f_71, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.06/1.59  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.06/1.59  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.06/1.59  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.06/1.59  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.06/1.59  tff(f_29, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.06/1.59  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.06/1.59  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.06/1.59  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.59  tff(c_41, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 3.06/1.59  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.59  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 3.06/1.59  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.59  tff(c_59, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.59  tff(c_62, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_59])).
% 3.06/1.59  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.59  tff(c_418, plain, (![B_46, C_47, A_48]: (k2_tarski(B_46, C_47)=A_48 | k1_tarski(C_47)=A_48 | k1_tarski(B_46)=A_48 | k1_xboole_0=A_48 | ~r1_tarski(A_48, k2_tarski(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.06/1.59  tff(c_444, plain, (![A_8, A_48]: (k2_tarski(A_8, A_8)=A_48 | k1_tarski(A_8)=A_48 | k1_tarski(A_8)=A_48 | k1_xboole_0=A_48 | ~r1_tarski(A_48, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_418])).
% 3.06/1.59  tff(c_597, plain, (![A_55, A_56]: (k1_tarski(A_55)=A_56 | k1_tarski(A_55)=A_56 | k1_tarski(A_55)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_tarski(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_444])).
% 3.06/1.59  tff(c_611, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_62, c_597])).
% 3.06/1.59  tff(c_620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_40, c_40, c_40, c_611])).
% 3.06/1.59  tff(c_621, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 3.06/1.59  tff(c_622, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 3.06/1.59  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.59  tff(c_623, plain, (![A_1]: (k4_xboole_0(A_1, '#skF_2')=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_622, c_2])).
% 3.06/1.59  tff(c_815, plain, (![A_79, B_80]: (k4_xboole_0(k2_xboole_0(A_79, B_80), B_80)=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.59  tff(c_822, plain, (![A_79]: (k4_xboole_0(A_79, '#skF_2')=k2_xboole_0(A_79, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_815, c_623])).
% 3.06/1.59  tff(c_837, plain, (![A_79]: (k2_xboole_0(A_79, '#skF_2')=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_822])).
% 3.06/1.59  tff(c_8, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.59  tff(c_724, plain, (![A_71, B_72]: (k3_tarski(k2_tarski(A_71, B_72))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.06/1.59  tff(c_789, plain, (![B_77, A_78]: (k3_tarski(k2_tarski(B_77, A_78))=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_8, c_724])).
% 3.06/1.59  tff(c_22, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.06/1.59  tff(c_864, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_789, c_22])).
% 3.06/1.59  tff(c_893, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_864, c_30])).
% 3.06/1.59  tff(c_931, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_837, c_893])).
% 3.06/1.59  tff(c_933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_621, c_931])).
% 3.06/1.59  tff(c_934, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 3.06/1.59  tff(c_935, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 3.06/1.59  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.59  tff(c_989, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_935, c_935, c_28])).
% 3.06/1.59  tff(c_957, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_935, c_30])).
% 3.06/1.59  tff(c_1100, plain, (![A_102, B_103]: (k3_tarski(k2_tarski(A_102, B_103))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.06/1.59  tff(c_1239, plain, (![B_112, A_113]: (k3_tarski(k2_tarski(B_112, A_113))=k2_xboole_0(A_113, B_112))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1100])).
% 3.06/1.59  tff(c_1313, plain, (![B_117, A_118]: (k2_xboole_0(B_117, A_118)=k2_xboole_0(A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_22])).
% 3.06/1.59  tff(c_1375, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_957, c_1313])).
% 3.06/1.59  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.59  tff(c_1443, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1375, c_6])).
% 3.06/1.59  tff(c_1265, plain, (![B_114, C_115, A_116]: (k2_tarski(B_114, C_115)=A_116 | k1_tarski(C_115)=A_116 | k1_tarski(B_114)=A_116 | k1_xboole_0=A_116 | ~r1_tarski(A_116, k2_tarski(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.06/1.59  tff(c_1293, plain, (![A_8, A_116]: (k2_tarski(A_8, A_8)=A_116 | k1_tarski(A_8)=A_116 | k1_tarski(A_8)=A_116 | k1_xboole_0=A_116 | ~r1_tarski(A_116, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1265])).
% 3.06/1.59  tff(c_1596, plain, (![A_127, A_128]: (k1_tarski(A_127)=A_128 | k1_tarski(A_127)=A_128 | k1_tarski(A_127)=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, k1_tarski(A_127)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1293])).
% 3.06/1.59  tff(c_1607, plain, (![A_128]: (k1_tarski('#skF_1')=A_128 | k1_tarski('#skF_1')=A_128 | k1_tarski('#skF_1')=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_935, c_1596])).
% 3.06/1.59  tff(c_1614, plain, (![A_129]: (A_129='#skF_2' | A_129='#skF_2' | A_129='#skF_2' | k1_xboole_0=A_129 | ~r1_tarski(A_129, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_935, c_935, c_935, c_1607])).
% 3.06/1.59  tff(c_1617, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1443, c_1614])).
% 3.06/1.59  tff(c_1629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_934, c_989, c_989, c_989, c_1617])).
% 3.06/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.59  
% 3.06/1.59  Inference rules
% 3.06/1.59  ----------------------
% 3.06/1.59  #Ref     : 0
% 3.06/1.59  #Sup     : 393
% 3.06/1.59  #Fact    : 0
% 3.06/1.59  #Define  : 0
% 3.06/1.59  #Split   : 3
% 3.06/1.59  #Chain   : 0
% 3.06/1.59  #Close   : 0
% 3.06/1.59  
% 3.06/1.59  Ordering : KBO
% 3.06/1.59  
% 3.06/1.59  Simplification rules
% 3.06/1.59  ----------------------
% 3.06/1.59  #Subsume      : 11
% 3.06/1.59  #Demod        : 197
% 3.06/1.59  #Tautology    : 307
% 3.06/1.59  #SimpNegUnit  : 5
% 3.06/1.59  #BackRed      : 1
% 3.06/1.59  
% 3.06/1.59  #Partial instantiations: 0
% 3.06/1.59  #Strategies tried      : 1
% 3.06/1.59  
% 3.06/1.59  Timing (in seconds)
% 3.06/1.59  ----------------------
% 3.06/1.60  Preprocessing        : 0.31
% 3.06/1.60  Parsing              : 0.16
% 3.06/1.60  CNF conversion       : 0.02
% 3.06/1.60  Main loop            : 0.45
% 3.06/1.60  Inferencing          : 0.16
% 3.06/1.60  Reduction            : 0.16
% 3.06/1.60  Demodulation         : 0.13
% 3.06/1.60  BG Simplification    : 0.02
% 3.06/1.60  Subsumption          : 0.06
% 3.06/1.60  Abstraction          : 0.02
% 3.06/1.60  MUC search           : 0.00
% 3.06/1.60  Cooper               : 0.00
% 3.06/1.60  Total                : 0.79
% 3.06/1.60  Index Insertion      : 0.00
% 3.06/1.60  Index Deletion       : 0.00
% 3.06/1.60  Index Matching       : 0.00
% 3.06/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
