%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:54 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 113 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [C_44,A_42,B_43] :
      ( r1_tarski(k9_relat_1(C_44,A_42),k9_relat_1(C_44,B_43))
      | ~ r1_tarski(A_42,B_43)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_24,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    ! [B_61,A_62] : k3_xboole_0(B_61,A_62) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_24])).

tff(c_152,plain,(
    ! [B_61,A_62] : r1_tarski(k3_xboole_0(B_61,A_62),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_6])).

tff(c_28,plain,(
    ! [B_46,A_45] :
      ( r1_tarski(k9_relat_1(B_46,k10_relat_1(B_46,A_45)),A_45)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_453,plain,(
    ! [C_106,A_107,B_108] :
      ( r1_tarski(k9_relat_1(C_106,A_107),k9_relat_1(C_106,B_108))
      | ~ r1_tarski(A_107,B_108)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1849,plain,(
    ! [C_200,A_201,B_202] :
      ( k2_xboole_0(k9_relat_1(C_200,A_201),k9_relat_1(C_200,B_202)) = k9_relat_1(C_200,B_202)
      | ~ r1_tarski(A_201,B_202)
      | ~ v1_relat_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_453,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3107,plain,(
    ! [C_291,A_292,C_293,B_294] :
      ( r1_tarski(k9_relat_1(C_291,A_292),C_293)
      | ~ r1_tarski(k9_relat_1(C_291,B_294),C_293)
      | ~ r1_tarski(A_292,B_294)
      | ~ v1_relat_1(C_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1849,c_2])).

tff(c_6219,plain,(
    ! [B_436,A_437,A_438] :
      ( r1_tarski(k9_relat_1(B_436,A_437),A_438)
      | ~ r1_tarski(A_437,k10_relat_1(B_436,A_438))
      | ~ v1_funct_1(B_436)
      | ~ v1_relat_1(B_436) ) ),
    inference(resolution,[status(thm)],[c_28,c_3107])).

tff(c_343,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(A_87,k3_xboole_0(B_88,C_89))
      | ~ r1_tarski(A_87,C_89)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_24])).

tff(c_30,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_130,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_30])).

tff(c_360,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_343,c_130])).

tff(c_569,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_6265,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6219,c_569])).

tff(c_6296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_152,c_6265])).

tff(c_6297,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_6347,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_6297])).

tff(c_6351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6,c_6347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.45  
% 6.47/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.46  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.47/2.46  
% 6.47/2.46  %Foreground sorts:
% 6.47/2.46  
% 6.47/2.46  
% 6.47/2.46  %Background operators:
% 6.47/2.46  
% 6.47/2.46  
% 6.47/2.46  %Foreground operators:
% 6.47/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.47/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.47/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.47/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.47/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.47/2.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.47/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.47/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.47/2.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.47/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.47/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.47/2.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.47/2.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.47/2.46  
% 6.47/2.47  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 6.47/2.47  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.47/2.47  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 6.47/2.47  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.47/2.47  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.47/2.47  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 6.47/2.47  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.47/2.47  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.47/2.47  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.47/2.47  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.47/2.47  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.47/2.47  tff(c_26, plain, (![C_44, A_42, B_43]: (r1_tarski(k9_relat_1(C_44, A_42), k9_relat_1(C_44, B_43)) | ~r1_tarski(A_42, B_43) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.47/2.47  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.47/2.47  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.47  tff(c_74, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.47/2.47  tff(c_107, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_10, c_74])).
% 6.47/2.47  tff(c_24, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.47/2.47  tff(c_131, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_107, c_24])).
% 6.47/2.47  tff(c_152, plain, (![B_61, A_62]: (r1_tarski(k3_xboole_0(B_61, A_62), A_62))), inference(superposition, [status(thm), theory('equality')], [c_131, c_6])).
% 6.47/2.47  tff(c_28, plain, (![B_46, A_45]: (r1_tarski(k9_relat_1(B_46, k10_relat_1(B_46, A_45)), A_45) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.47/2.47  tff(c_453, plain, (![C_106, A_107, B_108]: (r1_tarski(k9_relat_1(C_106, A_107), k9_relat_1(C_106, B_108)) | ~r1_tarski(A_107, B_108) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.47/2.47  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.47/2.47  tff(c_1849, plain, (![C_200, A_201, B_202]: (k2_xboole_0(k9_relat_1(C_200, A_201), k9_relat_1(C_200, B_202))=k9_relat_1(C_200, B_202) | ~r1_tarski(A_201, B_202) | ~v1_relat_1(C_200))), inference(resolution, [status(thm)], [c_453, c_4])).
% 6.47/2.47  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.47  tff(c_3107, plain, (![C_291, A_292, C_293, B_294]: (r1_tarski(k9_relat_1(C_291, A_292), C_293) | ~r1_tarski(k9_relat_1(C_291, B_294), C_293) | ~r1_tarski(A_292, B_294) | ~v1_relat_1(C_291))), inference(superposition, [status(thm), theory('equality')], [c_1849, c_2])).
% 6.47/2.47  tff(c_6219, plain, (![B_436, A_437, A_438]: (r1_tarski(k9_relat_1(B_436, A_437), A_438) | ~r1_tarski(A_437, k10_relat_1(B_436, A_438)) | ~v1_funct_1(B_436) | ~v1_relat_1(B_436))), inference(resolution, [status(thm)], [c_28, c_3107])).
% 6.47/2.47  tff(c_343, plain, (![A_87, B_88, C_89]: (r1_tarski(A_87, k3_xboole_0(B_88, C_89)) | ~r1_tarski(A_87, C_89) | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.47  tff(c_113, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_107, c_24])).
% 6.47/2.47  tff(c_30, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.47/2.47  tff(c_130, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_30])).
% 6.47/2.47  tff(c_360, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_343, c_130])).
% 6.47/2.47  tff(c_569, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_360])).
% 6.47/2.47  tff(c_6265, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6219, c_569])).
% 6.47/2.47  tff(c_6296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_152, c_6265])).
% 6.47/2.47  tff(c_6297, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_360])).
% 6.47/2.47  tff(c_6347, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_6297])).
% 6.47/2.47  tff(c_6351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6, c_6347])).
% 6.47/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.47  
% 6.47/2.47  Inference rules
% 6.47/2.47  ----------------------
% 6.47/2.47  #Ref     : 0
% 6.47/2.47  #Sup     : 1559
% 6.47/2.47  #Fact    : 0
% 6.47/2.47  #Define  : 0
% 6.47/2.47  #Split   : 1
% 6.47/2.47  #Chain   : 0
% 6.47/2.47  #Close   : 0
% 6.47/2.47  
% 6.47/2.47  Ordering : KBO
% 6.47/2.47  
% 6.47/2.47  Simplification rules
% 6.47/2.47  ----------------------
% 6.47/2.47  #Subsume      : 84
% 6.47/2.47  #Demod        : 310
% 6.47/2.47  #Tautology    : 597
% 6.47/2.47  #SimpNegUnit  : 0
% 6.47/2.47  #BackRed      : 1
% 6.47/2.47  
% 6.47/2.47  #Partial instantiations: 0
% 6.47/2.47  #Strategies tried      : 1
% 6.47/2.47  
% 6.47/2.47  Timing (in seconds)
% 6.47/2.47  ----------------------
% 6.47/2.47  Preprocessing        : 0.30
% 6.47/2.47  Parsing              : 0.16
% 6.47/2.47  CNF conversion       : 0.02
% 6.47/2.47  Main loop            : 1.37
% 6.47/2.47  Inferencing          : 0.35
% 6.47/2.47  Reduction            : 0.58
% 6.47/2.47  Demodulation         : 0.50
% 6.47/2.47  BG Simplification    : 0.05
% 6.47/2.47  Subsumption          : 0.31
% 6.47/2.47  Abstraction          : 0.05
% 6.47/2.47  MUC search           : 0.00
% 6.47/2.47  Cooper               : 0.00
% 6.47/2.47  Total                : 1.69
% 6.47/2.47  Index Insertion      : 0.00
% 6.47/2.47  Index Deletion       : 0.00
% 6.47/2.47  Index Matching       : 0.00
% 6.47/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
