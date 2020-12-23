%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   58 (  67 expanded)
%              Number of leaves         :   33 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 (  70 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_81,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_40,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_38] : k1_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_35] : v1_relat_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_262,plain,(
    ! [B_82,A_83] : k5_relat_1(k6_relat_1(B_82),k6_relat_1(A_83)) = k6_relat_1(k3_xboole_0(A_83,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( k5_relat_1(k6_relat_1(A_41),B_42) = k7_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_268,plain,(
    ! [A_83,B_82] :
      ( k7_relat_1(k6_relat_1(A_83),B_82) = k6_relat_1(k3_xboole_0(A_83,B_82))
      | ~ v1_relat_1(k6_relat_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_30])).

tff(c_278,plain,(
    ! [A_83,B_82] : k7_relat_1(k6_relat_1(A_83),B_82) = k6_relat_1(k3_xboole_0(A_83,B_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_268])).

tff(c_320,plain,(
    ! [B_86,A_87] :
      ( k7_relat_1(B_86,A_87) = B_86
      | ~ r1_tarski(k1_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_330,plain,(
    ! [A_38,A_87] :
      ( k7_relat_1(k6_relat_1(A_38),A_87) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_87)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_320])).

tff(c_914,plain,(
    ! [A_132,A_133] :
      ( k6_relat_1(k3_xboole_0(A_132,A_133)) = k6_relat_1(A_132)
      | ~ r1_tarski(A_132,A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_278,c_330])).

tff(c_935,plain,(
    ! [A_132,A_133] :
      ( k3_xboole_0(A_132,A_133) = k1_relat_1(k6_relat_1(A_132))
      | ~ r1_tarski(A_132,A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_24])).

tff(c_968,plain,(
    ! [A_134,A_135] :
      ( k3_xboole_0(A_134,A_135) = A_134
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_935])).

tff(c_1031,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_968])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [B_66,A_67] : k1_setfam_1(k2_tarski(B_66,A_67)) = k3_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_18,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    ! [B_66,A_67] : k3_xboole_0(B_66,A_67) = k3_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_18])).

tff(c_1208,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_161])).

tff(c_36,plain,(
    ! [A_46,C_48,B_47] :
      ( k3_xboole_0(A_46,k10_relat_1(C_48,B_47)) = k10_relat_1(k7_relat_1(C_48,A_46),B_47)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1368,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1208,c_36])).

tff(c_1396,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1368])).

tff(c_1398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.52  
% 3.25/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.52  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.52  
% 3.25/1.52  %Foreground sorts:
% 3.25/1.52  
% 3.25/1.52  
% 3.25/1.52  %Background operators:
% 3.25/1.52  
% 3.25/1.52  
% 3.25/1.52  %Foreground operators:
% 3.25/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.25/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.25/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.25/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.25/1.52  
% 3.35/1.53  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.35/1.53  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.35/1.53  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.35/1.53  tff(f_81, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.35/1.53  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.35/1.53  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.35/1.53  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.35/1.53  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.35/1.53  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.35/1.53  tff(c_40, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.53  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.53  tff(c_42, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.53  tff(c_24, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.53  tff(c_20, plain, (![A_35]: (v1_relat_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.53  tff(c_262, plain, (![B_82, A_83]: (k5_relat_1(k6_relat_1(B_82), k6_relat_1(A_83))=k6_relat_1(k3_xboole_0(A_83, B_82)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.35/1.53  tff(c_30, plain, (![A_41, B_42]: (k5_relat_1(k6_relat_1(A_41), B_42)=k7_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.35/1.53  tff(c_268, plain, (![A_83, B_82]: (k7_relat_1(k6_relat_1(A_83), B_82)=k6_relat_1(k3_xboole_0(A_83, B_82)) | ~v1_relat_1(k6_relat_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_262, c_30])).
% 3.35/1.53  tff(c_278, plain, (![A_83, B_82]: (k7_relat_1(k6_relat_1(A_83), B_82)=k6_relat_1(k3_xboole_0(A_83, B_82)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_268])).
% 3.35/1.53  tff(c_320, plain, (![B_86, A_87]: (k7_relat_1(B_86, A_87)=B_86 | ~r1_tarski(k1_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.35/1.53  tff(c_330, plain, (![A_38, A_87]: (k7_relat_1(k6_relat_1(A_38), A_87)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_87) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_320])).
% 3.35/1.53  tff(c_914, plain, (![A_132, A_133]: (k6_relat_1(k3_xboole_0(A_132, A_133))=k6_relat_1(A_132) | ~r1_tarski(A_132, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_278, c_330])).
% 3.35/1.53  tff(c_935, plain, (![A_132, A_133]: (k3_xboole_0(A_132, A_133)=k1_relat_1(k6_relat_1(A_132)) | ~r1_tarski(A_132, A_133))), inference(superposition, [status(thm), theory('equality')], [c_914, c_24])).
% 3.35/1.53  tff(c_968, plain, (![A_134, A_135]: (k3_xboole_0(A_134, A_135)=A_134 | ~r1_tarski(A_134, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_935])).
% 3.35/1.53  tff(c_1031, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_968])).
% 3.35/1.53  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.35/1.53  tff(c_100, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.53  tff(c_155, plain, (![B_66, A_67]: (k1_setfam_1(k2_tarski(B_66, A_67))=k3_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_4, c_100])).
% 3.35/1.53  tff(c_18, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.53  tff(c_161, plain, (![B_66, A_67]: (k3_xboole_0(B_66, A_67)=k3_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_155, c_18])).
% 3.35/1.53  tff(c_1208, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1031, c_161])).
% 3.35/1.53  tff(c_36, plain, (![A_46, C_48, B_47]: (k3_xboole_0(A_46, k10_relat_1(C_48, B_47))=k10_relat_1(k7_relat_1(C_48, A_46), B_47) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.35/1.53  tff(c_1368, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1208, c_36])).
% 3.35/1.53  tff(c_1396, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1368])).
% 3.35/1.53  tff(c_1398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1396])).
% 3.35/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  Inference rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Ref     : 0
% 3.35/1.53  #Sup     : 321
% 3.35/1.53  #Fact    : 0
% 3.35/1.53  #Define  : 0
% 3.35/1.53  #Split   : 0
% 3.35/1.53  #Chain   : 0
% 3.35/1.53  #Close   : 0
% 3.35/1.53  
% 3.35/1.53  Ordering : KBO
% 3.35/1.53  
% 3.35/1.53  Simplification rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Subsume      : 11
% 3.35/1.53  #Demod        : 167
% 3.35/1.53  #Tautology    : 183
% 3.35/1.53  #SimpNegUnit  : 1
% 3.35/1.53  #BackRed      : 0
% 3.35/1.53  
% 3.35/1.53  #Partial instantiations: 0
% 3.35/1.53  #Strategies tried      : 1
% 3.35/1.53  
% 3.35/1.53  Timing (in seconds)
% 3.35/1.53  ----------------------
% 3.35/1.53  Preprocessing        : 0.32
% 3.35/1.53  Parsing              : 0.17
% 3.35/1.53  CNF conversion       : 0.02
% 3.35/1.53  Main loop            : 0.40
% 3.35/1.53  Inferencing          : 0.14
% 3.35/1.53  Reduction            : 0.15
% 3.35/1.53  Demodulation         : 0.12
% 3.35/1.53  BG Simplification    : 0.02
% 3.35/1.53  Subsumption          : 0.06
% 3.35/1.53  Abstraction          : 0.02
% 3.35/1.53  MUC search           : 0.00
% 3.35/1.53  Cooper               : 0.00
% 3.35/1.53  Total                : 0.75
% 3.35/1.53  Index Insertion      : 0.00
% 3.35/1.53  Index Deletion       : 0.00
% 3.35/1.53  Index Matching       : 0.00
% 3.35/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
