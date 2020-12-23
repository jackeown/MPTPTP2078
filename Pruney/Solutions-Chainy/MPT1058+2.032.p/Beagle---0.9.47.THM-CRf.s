%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   62 (  73 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :   66 (  88 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    k2_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = A_39
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_105,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_106,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_115,plain,(
    ! [A_41] : r1_tarski(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_10])).

tff(c_263,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(k2_xboole_0(A_52,B_54),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_547,plain,(
    ! [A_71,B_72] : r1_tarski(A_71,k2_xboole_0(A_71,B_72)) ),
    inference(resolution,[status(thm)],[c_115,c_263])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(k2_xboole_0(A_4,B_5),C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_994,plain,(
    ! [A_88,B_89,B_90] : r1_tarski(A_88,k2_xboole_0(k2_xboole_0(A_88,B_89),B_90)) ),
    inference(resolution,[status(thm)],[c_547,c_6])).

tff(c_1178,plain,(
    ! [A_99,B_100,B_101] : r1_tarski(k4_xboole_0(A_99,B_100),k2_xboole_0(A_99,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_994])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [B_42,A_43] :
      ( ~ r1_xboole_0(B_42,A_43)
      | ~ r1_tarski(B_42,A_43)
      | v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(k4_xboole_0(A_16,B_17),B_17)
      | v1_xboole_0(k4_xboole_0(A_16,B_17)) ) ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_1234,plain,(
    ! [A_102,B_103] : v1_xboole_0(k4_xboole_0(A_102,k2_xboole_0(A_102,B_103))) ),
    inference(resolution,[status(thm)],[c_1178,c_136])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1268,plain,(
    ! [A_104,B_105] : k4_xboole_0(A_104,k2_xboole_0(A_104,B_105)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1234,c_4])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1294,plain,(
    ! [A_104,B_105] : k3_xboole_0(A_104,k2_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_12])).

tff(c_1883,plain,(
    ! [A_121,B_122] : k3_xboole_0(A_121,k2_xboole_0(A_121,B_122)) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1294])).

tff(c_1948,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1883])).

tff(c_382,plain,(
    ! [A_60,C_61,B_62] :
      ( k3_xboole_0(A_60,k10_relat_1(C_61,B_62)) = k10_relat_1(k7_relat_1(C_61,A_60),B_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_395,plain,(
    ! [C_61,B_62,A_60] :
      ( k3_xboole_0(k10_relat_1(C_61,B_62),A_60) = k10_relat_1(k7_relat_1(C_61,A_60),B_62)
      | ~ v1_relat_1(C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_2])).

tff(c_3103,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1948,c_395])).

tff(c_3169,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3103])).

tff(c_3171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_3169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.74  
% 3.73/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.74  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.73/1.74  
% 3.73/1.74  %Foreground sorts:
% 3.73/1.74  
% 3.73/1.74  
% 3.73/1.74  %Background operators:
% 3.73/1.74  
% 3.73/1.74  
% 3.73/1.74  %Foreground operators:
% 3.73/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.73/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.73/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.73/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.73/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.74  
% 3.73/1.75  tff(f_73, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.73/1.75  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.73/1.75  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.73/1.75  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.73/1.75  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.73/1.75  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.73/1.75  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.73/1.75  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.73/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.73/1.75  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.73/1.75  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.73/1.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.73/1.75  tff(c_26, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.75  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.75  tff(c_28, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.73/1.75  tff(c_70, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.73/1.75  tff(c_77, plain, (k2_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_28, c_70])).
% 3.73/1.75  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.73/1.75  tff(c_93, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=A_39 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.73/1.75  tff(c_105, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(resolution, [status(thm)], [c_14, c_93])).
% 3.73/1.75  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.75  tff(c_78, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_10, c_70])).
% 3.73/1.75  tff(c_106, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=A_41)), inference(resolution, [status(thm)], [c_14, c_93])).
% 3.73/1.75  tff(c_115, plain, (![A_41]: (r1_tarski(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_106, c_10])).
% 3.73/1.75  tff(c_263, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(k2_xboole_0(A_52, B_54), C_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.75  tff(c_547, plain, (![A_71, B_72]: (r1_tarski(A_71, k2_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_115, c_263])).
% 3.73/1.75  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(k2_xboole_0(A_4, B_5), C_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.75  tff(c_994, plain, (![A_88, B_89, B_90]: (r1_tarski(A_88, k2_xboole_0(k2_xboole_0(A_88, B_89), B_90)))), inference(resolution, [status(thm)], [c_547, c_6])).
% 3.73/1.75  tff(c_1178, plain, (![A_99, B_100, B_101]: (r1_tarski(k4_xboole_0(A_99, B_100), k2_xboole_0(A_99, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_994])).
% 3.73/1.75  tff(c_18, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.73/1.75  tff(c_125, plain, (![B_42, A_43]: (~r1_xboole_0(B_42, A_43) | ~r1_tarski(B_42, A_43) | v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.73/1.75  tff(c_136, plain, (![A_16, B_17]: (~r1_tarski(k4_xboole_0(A_16, B_17), B_17) | v1_xboole_0(k4_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_18, c_125])).
% 3.73/1.75  tff(c_1234, plain, (![A_102, B_103]: (v1_xboole_0(k4_xboole_0(A_102, k2_xboole_0(A_102, B_103))))), inference(resolution, [status(thm)], [c_1178, c_136])).
% 3.73/1.75  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.75  tff(c_1268, plain, (![A_104, B_105]: (k4_xboole_0(A_104, k2_xboole_0(A_104, B_105))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1234, c_4])).
% 3.73/1.75  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.73/1.75  tff(c_1294, plain, (![A_104, B_105]: (k3_xboole_0(A_104, k2_xboole_0(A_104, B_105))=k4_xboole_0(A_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1268, c_12])).
% 3.73/1.75  tff(c_1883, plain, (![A_121, B_122]: (k3_xboole_0(A_121, k2_xboole_0(A_121, B_122))=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1294])).
% 3.73/1.75  tff(c_1948, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_1883])).
% 3.73/1.75  tff(c_382, plain, (![A_60, C_61, B_62]: (k3_xboole_0(A_60, k10_relat_1(C_61, B_62))=k10_relat_1(k7_relat_1(C_61, A_60), B_62) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.73/1.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.73/1.75  tff(c_395, plain, (![C_61, B_62, A_60]: (k3_xboole_0(k10_relat_1(C_61, B_62), A_60)=k10_relat_1(k7_relat_1(C_61, A_60), B_62) | ~v1_relat_1(C_61))), inference(superposition, [status(thm), theory('equality')], [c_382, c_2])).
% 3.73/1.75  tff(c_3103, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1948, c_395])).
% 3.73/1.75  tff(c_3169, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3103])).
% 3.73/1.75  tff(c_3171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_3169])).
% 3.73/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.75  
% 3.73/1.75  Inference rules
% 3.73/1.75  ----------------------
% 3.73/1.75  #Ref     : 0
% 3.73/1.75  #Sup     : 769
% 3.73/1.75  #Fact    : 0
% 3.73/1.75  #Define  : 0
% 3.73/1.75  #Split   : 2
% 3.73/1.75  #Chain   : 0
% 3.73/1.75  #Close   : 0
% 3.73/1.75  
% 3.73/1.75  Ordering : KBO
% 3.73/1.75  
% 3.73/1.75  Simplification rules
% 3.73/1.75  ----------------------
% 3.73/1.75  #Subsume      : 12
% 3.73/1.75  #Demod        : 588
% 3.73/1.75  #Tautology    : 505
% 3.73/1.75  #SimpNegUnit  : 1
% 3.73/1.75  #BackRed      : 8
% 3.73/1.75  
% 3.73/1.75  #Partial instantiations: 0
% 3.73/1.75  #Strategies tried      : 1
% 3.73/1.75  
% 3.73/1.75  Timing (in seconds)
% 3.73/1.75  ----------------------
% 4.03/1.75  Preprocessing        : 0.33
% 4.03/1.75  Parsing              : 0.18
% 4.03/1.76  CNF conversion       : 0.02
% 4.03/1.76  Main loop            : 0.62
% 4.03/1.76  Inferencing          : 0.21
% 4.03/1.76  Reduction            : 0.25
% 4.03/1.76  Demodulation         : 0.20
% 4.03/1.76  BG Simplification    : 0.02
% 4.03/1.76  Subsumption          : 0.09
% 4.03/1.76  Abstraction          : 0.03
% 4.03/1.76  MUC search           : 0.00
% 4.03/1.76  Cooper               : 0.00
% 4.03/1.76  Total                : 0.99
% 4.03/1.76  Index Insertion      : 0.00
% 4.03/1.76  Index Deletion       : 0.00
% 4.03/1.76  Index Matching       : 0.00
% 4.03/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
