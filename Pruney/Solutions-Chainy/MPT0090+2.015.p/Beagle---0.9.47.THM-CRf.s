%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 103 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 117 expanded)
%              Number of equality atoms :   39 (  68 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_47])).

tff(c_32,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_82,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_25] : k3_xboole_0(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_82])).

tff(c_100,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_6])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_140,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_191,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k4_xboole_0(A_32,B_33),k3_xboole_0(A_32,C_34)) = k4_xboole_0(A_32,k4_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_206,plain,(
    ! [B_33] : k4_xboole_0('#skF_3',k4_xboole_0(B_33,'#skF_4')) = k2_xboole_0(k4_xboole_0('#skF_3',B_33),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_191])).

tff(c_328,plain,(
    ! [B_38] : k4_xboole_0('#skF_3',k4_xboole_0(B_38,'#skF_4')) = k4_xboole_0('#skF_3',B_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_206])).

tff(c_351,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_328])).

tff(c_356,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_351])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_356])).

tff(c_359,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_364,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_14])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_364])).

tff(c_369,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_374,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_14])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_374])).

tff(c_380,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_425,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_16])).

tff(c_390,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k2_xboole_0(A_41,B_42)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_400,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_390])).

tff(c_427,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_462,plain,(
    ! [A_47] : k3_xboole_0(A_47,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_427])).

tff(c_467,plain,(
    ! [A_47] : k2_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_6])).

tff(c_379,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_445,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_379,c_427])).

tff(c_559,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k4_xboole_0(A_54,B_55),k3_xboole_0(A_54,C_56)) = k4_xboole_0(A_54,k4_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_580,plain,(
    ! [B_55] : k4_xboole_0('#skF_3',k4_xboole_0(B_55,'#skF_4')) = k2_xboole_0(k4_xboole_0('#skF_3',B_55),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_559])).

tff(c_796,plain,(
    ! [B_63] : k4_xboole_0('#skF_3',k4_xboole_0(B_63,'#skF_4')) = k4_xboole_0('#skF_3',B_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_580])).

tff(c_828,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_796])).

tff(c_835,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_828])).

tff(c_837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.40  
% 2.35/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.40  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.40  
% 2.35/1.40  %Foreground sorts:
% 2.35/1.40  
% 2.35/1.40  
% 2.35/1.40  %Background operators:
% 2.35/1.40  
% 2.35/1.40  
% 2.35/1.40  %Foreground operators:
% 2.35/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.35/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.40  
% 2.35/1.42  tff(f_44, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.35/1.42  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.35/1.42  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.35/1.42  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.35/1.42  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.35/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.35/1.42  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.35/1.42  tff(c_20, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.42  tff(c_37, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 2.35/1.42  tff(c_18, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.42  tff(c_150, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 2.35/1.42  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.42  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.42  tff(c_47, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.42  tff(c_57, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_47])).
% 2.35/1.42  tff(c_32, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.42  tff(c_35, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_32])).
% 2.35/1.42  tff(c_82, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.42  tff(c_95, plain, (![A_25]: (k3_xboole_0(A_25, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_82])).
% 2.35/1.42  tff(c_100, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_95, c_6])).
% 2.35/1.42  tff(c_22, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.42  tff(c_136, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.35/1.42  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.42  tff(c_140, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_2])).
% 2.35/1.42  tff(c_191, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k4_xboole_0(A_32, B_33), k3_xboole_0(A_32, C_34))=k4_xboole_0(A_32, k4_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.42  tff(c_206, plain, (![B_33]: (k4_xboole_0('#skF_3', k4_xboole_0(B_33, '#skF_4'))=k2_xboole_0(k4_xboole_0('#skF_3', B_33), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_140, c_191])).
% 2.35/1.42  tff(c_328, plain, (![B_38]: (k4_xboole_0('#skF_3', k4_xboole_0(B_38, '#skF_4'))=k4_xboole_0('#skF_3', B_38))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_206])).
% 2.35/1.42  tff(c_351, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57, c_328])).
% 2.35/1.42  tff(c_356, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_351])).
% 2.35/1.42  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_356])).
% 2.35/1.42  tff(c_359, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 2.35/1.42  tff(c_14, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.42  tff(c_364, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_359, c_14])).
% 2.35/1.42  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_364])).
% 2.35/1.42  tff(c_369, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_22])).
% 2.35/1.42  tff(c_374, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_369, c_14])).
% 2.35/1.42  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_374])).
% 2.35/1.42  tff(c_380, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 2.35/1.42  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.42  tff(c_425, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_380, c_16])).
% 2.35/1.42  tff(c_390, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k2_xboole_0(A_41, B_42))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.42  tff(c_400, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_390])).
% 2.35/1.42  tff(c_427, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.42  tff(c_462, plain, (![A_47]: (k3_xboole_0(A_47, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_427])).
% 2.35/1.42  tff(c_467, plain, (![A_47]: (k2_xboole_0(A_47, k1_xboole_0)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_462, c_6])).
% 2.35/1.42  tff(c_379, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 2.35/1.42  tff(c_445, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_379, c_427])).
% 2.35/1.42  tff(c_559, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k4_xboole_0(A_54, B_55), k3_xboole_0(A_54, C_56))=k4_xboole_0(A_54, k4_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.42  tff(c_580, plain, (![B_55]: (k4_xboole_0('#skF_3', k4_xboole_0(B_55, '#skF_4'))=k2_xboole_0(k4_xboole_0('#skF_3', B_55), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_445, c_559])).
% 2.35/1.42  tff(c_796, plain, (![B_63]: (k4_xboole_0('#skF_3', k4_xboole_0(B_63, '#skF_4'))=k4_xboole_0('#skF_3', B_63))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_580])).
% 2.35/1.42  tff(c_828, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_400, c_796])).
% 2.35/1.42  tff(c_835, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_828])).
% 2.35/1.42  tff(c_837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_835])).
% 2.35/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.42  
% 2.35/1.42  Inference rules
% 2.35/1.42  ----------------------
% 2.35/1.42  #Ref     : 0
% 2.35/1.42  #Sup     : 206
% 2.35/1.42  #Fact    : 0
% 2.35/1.42  #Define  : 0
% 2.35/1.42  #Split   : 3
% 2.35/1.42  #Chain   : 0
% 2.35/1.42  #Close   : 0
% 2.35/1.42  
% 2.35/1.42  Ordering : KBO
% 2.35/1.42  
% 2.35/1.42  Simplification rules
% 2.35/1.42  ----------------------
% 2.35/1.42  #Subsume      : 2
% 2.35/1.42  #Demod        : 92
% 2.35/1.42  #Tautology    : 143
% 2.35/1.42  #SimpNegUnit  : 4
% 2.35/1.42  #BackRed      : 2
% 2.35/1.42  
% 2.35/1.42  #Partial instantiations: 0
% 2.35/1.42  #Strategies tried      : 1
% 2.35/1.42  
% 2.35/1.42  Timing (in seconds)
% 2.35/1.42  ----------------------
% 2.35/1.42  Preprocessing        : 0.31
% 2.35/1.42  Parsing              : 0.16
% 2.35/1.42  CNF conversion       : 0.02
% 2.35/1.42  Main loop            : 0.31
% 2.35/1.42  Inferencing          : 0.12
% 2.35/1.42  Reduction            : 0.10
% 2.35/1.42  Demodulation         : 0.08
% 2.35/1.42  BG Simplification    : 0.01
% 2.35/1.42  Subsumption          : 0.04
% 2.35/1.42  Abstraction          : 0.02
% 2.35/1.42  MUC search           : 0.00
% 2.35/1.42  Cooper               : 0.00
% 2.35/1.42  Total                : 0.65
% 2.35/1.42  Index Insertion      : 0.00
% 2.35/1.42  Index Deletion       : 0.00
% 2.35/1.42  Index Matching       : 0.00
% 2.35/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
