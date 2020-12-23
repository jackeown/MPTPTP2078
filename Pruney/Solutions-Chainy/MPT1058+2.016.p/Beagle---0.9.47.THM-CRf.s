%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   62 (  73 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 (  86 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_89,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_46,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1952,plain,(
    ! [A_147,C_148,B_149] :
      ( k3_xboole_0(A_147,k10_relat_1(C_148,B_149)) = k10_relat_1(k7_relat_1(C_148,A_147),B_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [B_67,A_68] : k1_setfam_1(k2_tarski(B_67,A_68)) = k3_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_117])).

tff(c_18,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_192,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_18])).

tff(c_48,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [A_37] : k1_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_41] : v1_relat_1(k6_relat_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_539,plain,(
    ! [B_107,A_108] : k5_relat_1(k6_relat_1(B_107),k6_relat_1(A_108)) = k6_relat_1(k3_xboole_0(A_108,B_107)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_relat_1(A_38),B_39) = k7_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_545,plain,(
    ! [A_108,B_107] :
      ( k7_relat_1(k6_relat_1(A_108),B_107) = k6_relat_1(k3_xboole_0(A_108,B_107))
      | ~ v1_relat_1(k6_relat_1(A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_34])).

tff(c_555,plain,(
    ! [A_108,B_107] : k7_relat_1(k6_relat_1(A_108),B_107) = k6_relat_1(k3_xboole_0(A_108,B_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_545])).

tff(c_248,plain,(
    ! [B_71,A_72] :
      ( v4_relat_1(B_71,A_72)
      | ~ r1_tarski(k1_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_251,plain,(
    ! [A_37,A_72] :
      ( v4_relat_1(k6_relat_1(A_37),A_72)
      | ~ r1_tarski(A_37,A_72)
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_248])).

tff(c_253,plain,(
    ! [A_37,A_72] :
      ( v4_relat_1(k6_relat_1(A_37),A_72)
      | ~ r1_tarski(A_37,A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_251])).

tff(c_769,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = B_116
      | ~ v4_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_772,plain,(
    ! [A_37,A_72] :
      ( k7_relat_1(k6_relat_1(A_37),A_72) = k6_relat_1(A_37)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ r1_tarski(A_37,A_72) ) ),
    inference(resolution,[status(thm)],[c_253,c_769])).

tff(c_852,plain,(
    ! [A_125,A_126] :
      ( k6_relat_1(k3_xboole_0(A_125,A_126)) = k6_relat_1(A_125)
      | ~ r1_tarski(A_125,A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_555,c_772])).

tff(c_885,plain,(
    ! [A_125,A_126] :
      ( k3_xboole_0(A_125,A_126) = k1_relat_1(k6_relat_1(A_125))
      | ~ r1_tarski(A_125,A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_30])).

tff(c_918,plain,(
    ! [A_127,A_128] :
      ( k3_xboole_0(A_127,A_128) = A_127
      | ~ r1_tarski(A_127,A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_885])).

tff(c_971,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_918])).

tff(c_1013,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_971])).

tff(c_1981,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1952,c_1013])).

tff(c_2104,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1981])).

tff(c_2106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:10:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.61  
% 3.40/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.62  %$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.62  
% 3.40/1.62  %Foreground sorts:
% 3.40/1.62  
% 3.40/1.62  
% 3.40/1.62  %Background operators:
% 3.40/1.62  
% 3.40/1.62  
% 3.40/1.62  %Foreground operators:
% 3.40/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.40/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.40/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.40/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.40/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/1.62  
% 3.40/1.63  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.40/1.63  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.40/1.63  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.40/1.63  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.40/1.63  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.40/1.63  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.40/1.63  tff(f_89, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.40/1.63  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.40/1.63  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.40/1.63  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.40/1.63  tff(c_46, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.63  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.63  tff(c_1952, plain, (![A_147, C_148, B_149]: (k3_xboole_0(A_147, k10_relat_1(C_148, B_149))=k10_relat_1(k7_relat_1(C_148, A_147), B_149) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.40/1.63  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.63  tff(c_117, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.63  tff(c_186, plain, (![B_67, A_68]: (k1_setfam_1(k2_tarski(B_67, A_68))=k3_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_6, c_117])).
% 3.40/1.63  tff(c_18, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.63  tff(c_192, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_186, c_18])).
% 3.40/1.63  tff(c_48, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.63  tff(c_30, plain, (![A_37]: (k1_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.40/1.63  tff(c_38, plain, (![A_41]: (v1_relat_1(k6_relat_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.40/1.63  tff(c_539, plain, (![B_107, A_108]: (k5_relat_1(k6_relat_1(B_107), k6_relat_1(A_108))=k6_relat_1(k3_xboole_0(A_108, B_107)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.40/1.63  tff(c_34, plain, (![A_38, B_39]: (k5_relat_1(k6_relat_1(A_38), B_39)=k7_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.63  tff(c_545, plain, (![A_108, B_107]: (k7_relat_1(k6_relat_1(A_108), B_107)=k6_relat_1(k3_xboole_0(A_108, B_107)) | ~v1_relat_1(k6_relat_1(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_539, c_34])).
% 3.40/1.63  tff(c_555, plain, (![A_108, B_107]: (k7_relat_1(k6_relat_1(A_108), B_107)=k6_relat_1(k3_xboole_0(A_108, B_107)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_545])).
% 3.40/1.63  tff(c_248, plain, (![B_71, A_72]: (v4_relat_1(B_71, A_72) | ~r1_tarski(k1_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.63  tff(c_251, plain, (![A_37, A_72]: (v4_relat_1(k6_relat_1(A_37), A_72) | ~r1_tarski(A_37, A_72) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_248])).
% 3.40/1.63  tff(c_253, plain, (![A_37, A_72]: (v4_relat_1(k6_relat_1(A_37), A_72) | ~r1_tarski(A_37, A_72))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_251])).
% 3.40/1.63  tff(c_769, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=B_116 | ~v4_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.63  tff(c_772, plain, (![A_37, A_72]: (k7_relat_1(k6_relat_1(A_37), A_72)=k6_relat_1(A_37) | ~v1_relat_1(k6_relat_1(A_37)) | ~r1_tarski(A_37, A_72))), inference(resolution, [status(thm)], [c_253, c_769])).
% 3.40/1.63  tff(c_852, plain, (![A_125, A_126]: (k6_relat_1(k3_xboole_0(A_125, A_126))=k6_relat_1(A_125) | ~r1_tarski(A_125, A_126))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_555, c_772])).
% 3.40/1.63  tff(c_885, plain, (![A_125, A_126]: (k3_xboole_0(A_125, A_126)=k1_relat_1(k6_relat_1(A_125)) | ~r1_tarski(A_125, A_126))), inference(superposition, [status(thm), theory('equality')], [c_852, c_30])).
% 3.40/1.63  tff(c_918, plain, (![A_127, A_128]: (k3_xboole_0(A_127, A_128)=A_127 | ~r1_tarski(A_127, A_128))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_885])).
% 3.40/1.63  tff(c_971, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_918])).
% 3.40/1.63  tff(c_1013, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_192, c_971])).
% 3.40/1.63  tff(c_1981, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1952, c_1013])).
% 3.40/1.63  tff(c_2104, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1981])).
% 3.40/1.63  tff(c_2106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2104])).
% 3.40/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.63  
% 3.40/1.63  Inference rules
% 3.40/1.63  ----------------------
% 3.40/1.63  #Ref     : 0
% 3.40/1.63  #Sup     : 493
% 3.40/1.63  #Fact    : 0
% 3.40/1.63  #Define  : 0
% 3.40/1.63  #Split   : 0
% 3.40/1.63  #Chain   : 0
% 3.40/1.63  #Close   : 0
% 3.40/1.63  
% 3.40/1.63  Ordering : KBO
% 3.40/1.63  
% 3.40/1.63  Simplification rules
% 3.40/1.63  ----------------------
% 3.40/1.63  #Subsume      : 18
% 3.40/1.63  #Demod        : 335
% 3.40/1.63  #Tautology    : 307
% 3.40/1.63  #SimpNegUnit  : 1
% 3.40/1.63  #BackRed      : 0
% 3.40/1.63  
% 3.40/1.63  #Partial instantiations: 0
% 3.40/1.63  #Strategies tried      : 1
% 3.40/1.63  
% 3.40/1.63  Timing (in seconds)
% 3.40/1.63  ----------------------
% 3.40/1.63  Preprocessing        : 0.34
% 3.40/1.63  Parsing              : 0.19
% 3.40/1.63  CNF conversion       : 0.02
% 3.40/1.63  Main loop            : 0.49
% 3.40/1.63  Inferencing          : 0.16
% 3.40/1.63  Reduction            : 0.21
% 3.40/1.63  Demodulation         : 0.17
% 3.40/1.63  BG Simplification    : 0.02
% 3.40/1.63  Subsumption          : 0.07
% 3.40/1.63  Abstraction          : 0.03
% 3.40/1.63  MUC search           : 0.00
% 3.40/1.63  Cooper               : 0.00
% 3.40/1.63  Total                : 0.86
% 3.40/1.63  Index Insertion      : 0.00
% 3.40/1.63  Index Deletion       : 0.00
% 3.40/1.63  Index Matching       : 0.00
% 3.40/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
