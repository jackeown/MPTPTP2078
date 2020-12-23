%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:53 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   54 (  77 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  94 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_74,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_110,plain,(
    ! [A_34,B_35] : k4_xboole_0(k2_xboole_0(A_34,B_35),k3_xboole_0(A_34,B_35)) = k5_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_1') = k5_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_110])).

tff(c_137,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_128])).

tff(c_248,plain,(
    ! [A_42,B_43] : k5_xboole_0(k5_xboole_0(A_42,B_43),k2_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_281,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_248])).

tff(c_293,plain,(
    k5_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_281])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_47])).

tff(c_87,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_96,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_87])).

tff(c_99,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_198,plain,(
    ! [A_40,B_41] : k2_xboole_0(k4_xboole_0(A_40,B_41),k4_xboole_0(B_41,A_40)) = k5_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_231,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_1'),k1_xboole_0) = k5_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_198])).

tff(c_235,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_231])).

tff(c_266,plain,(
    k5_xboole_0(k4_xboole_0('#skF_2','#skF_1'),k2_xboole_0('#skF_2','#skF_1')) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_248])).

tff(c_290,plain,(
    k5_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_2') = k3_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_266])).

tff(c_369,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_290])).

tff(c_378,plain,(
    ! [C_45,A_46,B_47] :
      ( k7_relat_1(k7_relat_1(C_45,A_46),B_47) = k7_relat_1(C_45,k3_xboole_0(A_46,B_47))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_387,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_24])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_369,c_387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:12:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.16/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.24  
% 2.16/1.26  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.16/1.26  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.16/1.26  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.26  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.16/1.26  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.16/1.26  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.16/1.26  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.16/1.26  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.16/1.26  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.16/1.26  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.16/1.26  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.16/1.26  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.26  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.26  tff(c_61, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.26  tff(c_69, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_61])).
% 2.16/1.26  tff(c_74, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.26  tff(c_82, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_26, c_74])).
% 2.16/1.26  tff(c_110, plain, (![A_34, B_35]: (k4_xboole_0(k2_xboole_0(A_34, B_35), k3_xboole_0(A_34, B_35))=k5_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.26  tff(c_128, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k5_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82, c_110])).
% 2.16/1.26  tff(c_137, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_128])).
% 2.16/1.26  tff(c_248, plain, (![A_42, B_43]: (k5_xboole_0(k5_xboole_0(A_42, B_43), k2_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.26  tff(c_281, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_69, c_248])).
% 2.16/1.26  tff(c_293, plain, (k5_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_281])).
% 2.16/1.26  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.26  tff(c_47, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.26  tff(c_51, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_47])).
% 2.16/1.26  tff(c_87, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.26  tff(c_96, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_51, c_87])).
% 2.16/1.26  tff(c_99, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96])).
% 2.16/1.26  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.26  tff(c_198, plain, (![A_40, B_41]: (k2_xboole_0(k4_xboole_0(A_40, B_41), k4_xboole_0(B_41, A_40))=k5_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.26  tff(c_231, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), k1_xboole_0)=k5_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_51, c_198])).
% 2.16/1.26  tff(c_235, plain, (k5_xboole_0('#skF_2', '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_231])).
% 2.16/1.26  tff(c_266, plain, (k5_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), k2_xboole_0('#skF_2', '#skF_1'))=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_235, c_248])).
% 2.16/1.26  tff(c_290, plain, (k5_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_266])).
% 2.16/1.26  tff(c_369, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_293, c_290])).
% 2.16/1.26  tff(c_378, plain, (![C_45, A_46, B_47]: (k7_relat_1(k7_relat_1(C_45, A_46), B_47)=k7_relat_1(C_45, k3_xboole_0(A_46, B_47)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.26  tff(c_24, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.26  tff(c_387, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_378, c_24])).
% 2.16/1.26  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_369, c_387])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 104
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 0
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 0
% 2.16/1.26  #Demod        : 40
% 2.16/1.26  #Tautology    : 58
% 2.16/1.26  #SimpNegUnit  : 0
% 2.16/1.26  #BackRed      : 1
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.26  Preprocessing        : 0.27
% 2.16/1.26  Parsing              : 0.16
% 2.16/1.26  CNF conversion       : 0.02
% 2.16/1.26  Main loop            : 0.23
% 2.16/1.26  Inferencing          : 0.09
% 2.16/1.26  Reduction            : 0.07
% 2.16/1.26  Demodulation         : 0.06
% 2.16/1.26  BG Simplification    : 0.01
% 2.16/1.26  Subsumption          : 0.03
% 2.16/1.26  Abstraction          : 0.01
% 2.16/1.26  MUC search           : 0.00
% 2.16/1.26  Cooper               : 0.00
% 2.16/1.26  Total                : 0.53
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
