%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:22 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 136 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_108,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_112,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_18])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_227,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_723,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(A_65,k2_xboole_0(k4_xboole_0(A_65,B_66),C_67)) = k4_xboole_0(k3_xboole_0(A_65,B_66),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_26,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_41,plain,(
    ! [A_21,B_20] : r1_tarski(A_21,k2_xboole_0(B_20,A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_113,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_21,B_20] : k4_xboole_0(A_21,k2_xboole_0(B_20,A_21)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_113])).

tff(c_751,plain,(
    ! [C_67,B_66] : k4_xboole_0(k3_xboole_0(C_67,B_66),C_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_124])).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_369,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(A_49,B_48)
      | ~ v1_zfmisc_1(B_48)
      | v1_xboole_0(B_48)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_519,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ v1_zfmisc_1(B_53)
      | v1_xboole_0(B_53)
      | v1_xboole_0(A_54)
      | k4_xboole_0(A_54,B_53) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_369])).

tff(c_521,plain,(
    ! [A_54] :
      ( A_54 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_54)
      | k4_xboole_0(A_54,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_519])).

tff(c_527,plain,(
    ! [A_55] :
      ( A_55 = '#skF_1'
      | v1_xboole_0(A_55)
      | k4_xboole_0(A_55,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_521])).

tff(c_20,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_534,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_527,c_20])).

tff(c_537,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_537])).

tff(c_822,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_997,plain,(
    ! [A_74,B_75,C_76] : k4_xboole_0(A_74,k2_xboole_0(k4_xboole_0(A_74,B_75),C_76)) = k4_xboole_0(k3_xboole_0(A_74,B_75),C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_227])).

tff(c_1092,plain,(
    ! [C_77,B_78] : k4_xboole_0(k3_xboole_0(C_77,B_78),C_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_124])).

tff(c_1289,plain,(
    ! [B_81,A_82] : k4_xboole_0(k3_xboole_0(B_81,A_82),A_82) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1092])).

tff(c_1326,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_1289])).

tff(c_1356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.14/1.50  
% 3.14/1.50  %Foreground sorts:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Background operators:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Foreground operators:
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.14/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.50  
% 3.14/1.52  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.14/1.52  tff(f_64, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 3.14/1.52  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.14/1.52  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.14/1.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.14/1.52  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.14/1.52  tff(f_52, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.14/1.52  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.14/1.52  tff(c_108, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.52  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.52  tff(c_112, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_18])).
% 3.14/1.52  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.52  tff(c_227, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.52  tff(c_723, plain, (![A_65, B_66, C_67]: (k4_xboole_0(A_65, k2_xboole_0(k4_xboole_0(A_65, B_66), C_67))=k4_xboole_0(k3_xboole_0(A_65, B_66), C_67))), inference(superposition, [status(thm), theory('equality')], [c_12, c_227])).
% 3.14/1.52  tff(c_26, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.52  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.52  tff(c_41, plain, (![A_21, B_20]: (r1_tarski(A_21, k2_xboole_0(B_20, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_14])).
% 3.14/1.52  tff(c_113, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.52  tff(c_124, plain, (![A_21, B_20]: (k4_xboole_0(A_21, k2_xboole_0(B_20, A_21))=k1_xboole_0)), inference(resolution, [status(thm)], [c_41, c_113])).
% 3.14/1.52  tff(c_751, plain, (![C_67, B_66]: (k4_xboole_0(k3_xboole_0(C_67, B_66), C_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_723, c_124])).
% 3.14/1.52  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.52  tff(c_22, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.52  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.14/1.52  tff(c_369, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(A_49, B_48) | ~v1_zfmisc_1(B_48) | v1_xboole_0(B_48) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.52  tff(c_519, plain, (![B_53, A_54]: (B_53=A_54 | ~v1_zfmisc_1(B_53) | v1_xboole_0(B_53) | v1_xboole_0(A_54) | k4_xboole_0(A_54, B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_369])).
% 3.14/1.52  tff(c_521, plain, (![A_54]: (A_54='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_54) | k4_xboole_0(A_54, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_519])).
% 3.14/1.52  tff(c_527, plain, (![A_55]: (A_55='#skF_1' | v1_xboole_0(A_55) | k4_xboole_0(A_55, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_24, c_521])).
% 3.14/1.52  tff(c_20, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.52  tff(c_534, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_527, c_20])).
% 3.14/1.52  tff(c_537, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_534])).
% 3.14/1.52  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_751, c_537])).
% 3.14/1.52  tff(c_822, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_534])).
% 3.14/1.52  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.52  tff(c_997, plain, (![A_74, B_75, C_76]: (k4_xboole_0(A_74, k2_xboole_0(k4_xboole_0(A_74, B_75), C_76))=k4_xboole_0(k3_xboole_0(A_74, B_75), C_76))), inference(superposition, [status(thm), theory('equality')], [c_12, c_227])).
% 3.14/1.52  tff(c_1092, plain, (![C_77, B_78]: (k4_xboole_0(k3_xboole_0(C_77, B_78), C_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_997, c_124])).
% 3.14/1.52  tff(c_1289, plain, (![B_81, A_82]: (k4_xboole_0(k3_xboole_0(B_81, A_82), A_82)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1092])).
% 3.14/1.52  tff(c_1326, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_822, c_1289])).
% 3.14/1.52  tff(c_1356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_1326])).
% 3.14/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.52  
% 3.14/1.52  Inference rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Ref     : 0
% 3.14/1.52  #Sup     : 338
% 3.14/1.52  #Fact    : 0
% 3.14/1.52  #Define  : 0
% 3.14/1.52  #Split   : 1
% 3.14/1.52  #Chain   : 0
% 3.14/1.52  #Close   : 0
% 3.14/1.52  
% 3.14/1.52  Ordering : KBO
% 3.14/1.52  
% 3.14/1.52  Simplification rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Subsume      : 3
% 3.14/1.52  #Demod        : 145
% 3.14/1.52  #Tautology    : 181
% 3.14/1.52  #SimpNegUnit  : 2
% 3.14/1.52  #BackRed      : 3
% 3.14/1.52  
% 3.14/1.52  #Partial instantiations: 0
% 3.14/1.52  #Strategies tried      : 1
% 3.14/1.52  
% 3.14/1.52  Timing (in seconds)
% 3.14/1.52  ----------------------
% 3.14/1.52  Preprocessing        : 0.28
% 3.14/1.52  Parsing              : 0.15
% 3.14/1.52  CNF conversion       : 0.02
% 3.14/1.52  Main loop            : 0.47
% 3.14/1.52  Inferencing          : 0.16
% 3.14/1.52  Reduction            : 0.19
% 3.14/1.52  Demodulation         : 0.16
% 3.14/1.52  BG Simplification    : 0.02
% 3.14/1.52  Subsumption          : 0.07
% 3.14/1.52  Abstraction          : 0.02
% 3.14/1.52  MUC search           : 0.00
% 3.14/1.52  Cooper               : 0.00
% 3.14/1.52  Total                : 0.78
% 3.14/1.52  Index Insertion      : 0.00
% 3.14/1.52  Index Deletion       : 0.00
% 3.14/1.52  Index Matching       : 0.00
% 3.14/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
