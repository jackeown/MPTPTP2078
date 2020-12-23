%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:42 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   32 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  68 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_173,plain,(
    ! [A_83,B_84] :
      ( k5_relat_1(k6_relat_1(A_83),B_84) = k7_relat_1(B_84,A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [B_46,A_45] : k5_relat_1(k6_relat_1(B_46),k6_relat_1(A_45)) = k6_relat_1(k3_xboole_0(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_180,plain,(
    ! [A_45,A_83] :
      ( k7_relat_1(k6_relat_1(A_45),A_83) = k6_relat_1(k3_xboole_0(A_45,A_83))
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_38])).

tff(c_189,plain,(
    ! [A_45,A_83] : k7_relat_1(k6_relat_1(A_45),A_83) = k6_relat_1(k3_xboole_0(A_45,A_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_180])).

tff(c_389,plain,(
    ! [B_108,A_109] :
      ( k7_relat_1(B_108,A_109) = B_108
      | ~ r1_tarski(k1_relat_1(B_108),A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_396,plain,(
    ! [A_40,A_109] :
      ( k7_relat_1(k6_relat_1(A_40),A_109) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_109)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_389])).

tff(c_555,plain,(
    ! [A_119,A_120] :
      ( k6_relat_1(k3_xboole_0(A_119,A_120)) = k6_relat_1(A_119)
      | ~ r1_tarski(A_119,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_189,c_396])).

tff(c_585,plain,(
    ! [A_119,A_120] :
      ( k3_xboole_0(A_119,A_120) = k1_relat_1(k6_relat_1(A_119))
      | ~ r1_tarski(A_119,A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_30])).

tff(c_608,plain,(
    ! [A_121,A_122] :
      ( k3_xboole_0(A_121,A_122) = A_121
      | ~ r1_tarski(A_121,A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_585])).

tff(c_637,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_608])).

tff(c_1207,plain,(
    ! [C_147,A_148,B_149] :
      ( k2_wellord1(k2_wellord1(C_147,A_148),B_149) = k2_wellord1(C_147,k3_xboole_0(A_148,B_149))
      | ~ v1_relat_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_873,plain,(
    ! [C_130,B_131,A_132] :
      ( k2_wellord1(k2_wellord1(C_130,B_131),A_132) = k2_wellord1(k2_wellord1(C_130,A_132),B_131)
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_900,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_46])).

tff(c_939,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_900])).

tff(c_1216,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_939])).

tff(c_1256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_637,c_1216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.54  
% 2.99/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.54  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.54  
% 2.99/1.54  %Foreground sorts:
% 2.99/1.54  
% 2.99/1.54  
% 2.99/1.54  %Background operators:
% 2.99/1.54  
% 2.99/1.54  
% 2.99/1.54  %Foreground operators:
% 2.99/1.54  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.99/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.99/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.54  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.54  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.99/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.99/1.54  
% 3.13/1.55  tff(f_96, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 3.13/1.55  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.13/1.55  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.13/1.55  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.13/1.55  tff(f_77, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.13/1.55  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.13/1.55  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 3.13/1.55  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 3.13/1.55  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.13/1.55  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.13/1.55  tff(c_30, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.55  tff(c_26, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.55  tff(c_173, plain, (![A_83, B_84]: (k5_relat_1(k6_relat_1(A_83), B_84)=k7_relat_1(B_84, A_83) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.55  tff(c_38, plain, (![B_46, A_45]: (k5_relat_1(k6_relat_1(B_46), k6_relat_1(A_45))=k6_relat_1(k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.55  tff(c_180, plain, (![A_45, A_83]: (k7_relat_1(k6_relat_1(A_45), A_83)=k6_relat_1(k3_xboole_0(A_45, A_83)) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_38])).
% 3.13/1.55  tff(c_189, plain, (![A_45, A_83]: (k7_relat_1(k6_relat_1(A_45), A_83)=k6_relat_1(k3_xboole_0(A_45, A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_180])).
% 3.13/1.55  tff(c_389, plain, (![B_108, A_109]: (k7_relat_1(B_108, A_109)=B_108 | ~r1_tarski(k1_relat_1(B_108), A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.13/1.55  tff(c_396, plain, (![A_40, A_109]: (k7_relat_1(k6_relat_1(A_40), A_109)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_109) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_389])).
% 3.13/1.55  tff(c_555, plain, (![A_119, A_120]: (k6_relat_1(k3_xboole_0(A_119, A_120))=k6_relat_1(A_119) | ~r1_tarski(A_119, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_189, c_396])).
% 3.13/1.55  tff(c_585, plain, (![A_119, A_120]: (k3_xboole_0(A_119, A_120)=k1_relat_1(k6_relat_1(A_119)) | ~r1_tarski(A_119, A_120))), inference(superposition, [status(thm), theory('equality')], [c_555, c_30])).
% 3.13/1.55  tff(c_608, plain, (![A_121, A_122]: (k3_xboole_0(A_121, A_122)=A_121 | ~r1_tarski(A_121, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_585])).
% 3.13/1.55  tff(c_637, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_48, c_608])).
% 3.13/1.55  tff(c_1207, plain, (![C_147, A_148, B_149]: (k2_wellord1(k2_wellord1(C_147, A_148), B_149)=k2_wellord1(C_147, k3_xboole_0(A_148, B_149)) | ~v1_relat_1(C_147))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.13/1.55  tff(c_873, plain, (![C_130, B_131, A_132]: (k2_wellord1(k2_wellord1(C_130, B_131), A_132)=k2_wellord1(k2_wellord1(C_130, A_132), B_131) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.13/1.55  tff(c_46, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.13/1.55  tff(c_900, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_873, c_46])).
% 3.13/1.55  tff(c_939, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_900])).
% 3.13/1.55  tff(c_1216, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1207, c_939])).
% 3.13/1.55  tff(c_1256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_637, c_1216])).
% 3.13/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.55  
% 3.13/1.55  Inference rules
% 3.13/1.55  ----------------------
% 3.13/1.55  #Ref     : 0
% 3.13/1.55  #Sup     : 284
% 3.13/1.55  #Fact    : 0
% 3.13/1.55  #Define  : 0
% 3.13/1.55  #Split   : 1
% 3.13/1.55  #Chain   : 0
% 3.13/1.55  #Close   : 0
% 3.13/1.55  
% 3.13/1.55  Ordering : KBO
% 3.13/1.55  
% 3.13/1.55  Simplification rules
% 3.13/1.55  ----------------------
% 3.13/1.55  #Subsume      : 34
% 3.13/1.55  #Demod        : 150
% 3.13/1.55  #Tautology    : 145
% 3.13/1.55  #SimpNegUnit  : 0
% 3.13/1.55  #BackRed      : 1
% 3.13/1.55  
% 3.13/1.55  #Partial instantiations: 0
% 3.13/1.55  #Strategies tried      : 1
% 3.13/1.55  
% 3.13/1.55  Timing (in seconds)
% 3.13/1.55  ----------------------
% 3.13/1.55  Preprocessing        : 0.33
% 3.13/1.55  Parsing              : 0.18
% 3.13/1.55  CNF conversion       : 0.02
% 3.13/1.55  Main loop            : 0.37
% 3.13/1.55  Inferencing          : 0.14
% 3.13/1.55  Reduction            : 0.11
% 3.13/1.55  Demodulation         : 0.09
% 3.13/1.55  BG Simplification    : 0.02
% 3.13/1.55  Subsumption          : 0.07
% 3.13/1.55  Abstraction          : 0.03
% 3.13/1.55  MUC search           : 0.00
% 3.13/1.55  Cooper               : 0.00
% 3.13/1.55  Total                : 0.73
% 3.13/1.55  Index Insertion      : 0.00
% 3.13/1.55  Index Deletion       : 0.00
% 3.13/1.55  Index Matching       : 0.00
% 3.13/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
