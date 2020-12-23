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
% DateTime   : Thu Dec  3 10:01:03 EST 2020

% Result     : Theorem 16.14s
% Output     : CNFRefutation 16.14s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 141 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 247 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    ! [A_35,B_34] : r1_tarski(A_35,k2_xboole_0(B_34,A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_210,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(k4_xboole_0(A_64,B_65),C_66)
      | ~ r1_tarski(A_64,k2_xboole_0(B_65,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_222,plain,(
    ! [A_67,C_68] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(A_67,k2_xboole_0(k1_xboole_0,C_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_210])).

tff(c_259,plain,(
    ! [C_69] : r1_tarski(k2_xboole_0(k1_xboole_0,C_69),C_69) ),
    inference(resolution,[status(thm)],[c_32,c_222])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_182,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(k2_xboole_0(A_56,B_57),A_56) ) ),
    inference(resolution,[status(thm)],[c_42,c_119])).

tff(c_188,plain,(
    ! [B_2,A_1] :
      ( k2_xboole_0(B_2,A_1) = B_2
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_294,plain,(
    ! [C_69] : k2_xboole_0(C_69,k1_xboole_0) = C_69 ),
    inference(resolution,[status(thm)],[c_259,c_188])).

tff(c_38,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(k4_xboole_0(A_18,B_19),C_20)
      | ~ r1_tarski(A_18,k2_xboole_0(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_178,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2300,plain,(
    ! [A_166,B_167,B_168] :
      ( r2_hidden('#skF_1'(A_166,B_167),B_168)
      | ~ r1_tarski(A_166,B_168)
      | r1_tarski(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39913,plain,(
    ! [A_833,B_834,B_835,B_836] :
      ( r2_hidden('#skF_1'(A_833,B_834),B_835)
      | ~ r1_tarski(B_836,B_835)
      | ~ r1_tarski(A_833,B_836)
      | r1_tarski(A_833,B_834) ) ),
    inference(resolution,[status(thm)],[c_2300,c_4])).

tff(c_40112,plain,(
    ! [A_837,B_838] :
      ( r2_hidden('#skF_1'(A_837,B_838),'#skF_5')
      | ~ r1_tarski(A_837,'#skF_4')
      | r1_tarski(A_837,B_838) ) ),
    inference(resolution,[status(thm)],[c_48,c_39913])).

tff(c_151,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_167,plain,(
    ! [A_8,B_9,B_49] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_8,B_9),B_49),B_9)
      | r1_tarski(k4_xboole_0(A_8,B_9),B_49) ) ),
    inference(resolution,[status(thm)],[c_151,c_12])).

tff(c_40262,plain,(
    ! [A_842,B_843] :
      ( ~ r1_tarski(k4_xboole_0(A_842,'#skF_5'),'#skF_4')
      | r1_tarski(k4_xboole_0(A_842,'#skF_5'),B_843) ) ),
    inference(resolution,[status(thm)],[c_40112,c_167])).

tff(c_40299,plain,(
    ! [A_18,B_843] :
      ( r1_tarski(k4_xboole_0(A_18,'#skF_5'),B_843)
      | ~ r1_tarski(A_18,k2_xboole_0('#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_40262])).

tff(c_40322,plain,(
    ! [A_844,B_845] :
      ( r1_tarski(k4_xboole_0(A_844,'#skF_5'),B_845)
      | ~ r1_tarski(A_844,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40299])).

tff(c_34,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_40430,plain,(
    ! [A_846] :
      ( k4_xboole_0(A_846,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_846,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40322,c_136])).

tff(c_40526,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_40430])).

tff(c_358,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(A_71,k2_xboole_0(B_72,C_73))
      | ~ r1_tarski(k4_xboole_0(A_71,B_72),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_517,plain,(
    ! [A_81,B_82] : r1_tarski(A_81,k2_xboole_0(B_82,k4_xboole_0(A_81,B_82))) ),
    inference(resolution,[status(thm)],[c_32,c_358])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_532,plain,(
    ! [B_82,A_81] :
      ( k2_xboole_0(B_82,k4_xboole_0(A_81,B_82)) = A_81
      | ~ r1_tarski(k2_xboole_0(B_82,k4_xboole_0(A_81,B_82)),A_81) ) ),
    inference(resolution,[status(thm)],[c_517,c_28])).

tff(c_40591,plain,
    ( k2_xboole_0('#skF_5',k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_5')) = k2_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski(k2_xboole_0('#skF_5',k1_xboole_0),k2_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40526,c_532])).

tff(c_40807,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_294,c_294,c_40526,c_40591])).

tff(c_474,plain,(
    ! [C_78,A_79,B_80] :
      ( k2_xboole_0(k9_relat_1(C_78,A_79),k9_relat_1(C_78,B_80)) = k9_relat_1(C_78,k2_xboole_0(A_79,B_80))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_501,plain,(
    ! [C_78,A_79,B_80] :
      ( r1_tarski(k9_relat_1(C_78,A_79),k9_relat_1(C_78,k2_xboole_0(A_79,B_80)))
      | ~ v1_relat_1(C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_42])).

tff(c_43960,plain,(
    ! [C_887] :
      ( r1_tarski(k9_relat_1(C_887,'#skF_4'),k9_relat_1(C_887,'#skF_5'))
      | ~ v1_relat_1(C_887) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40807,c_501])).

tff(c_46,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43970,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_43960,c_46])).

tff(c_43977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_43970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.14/7.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.14/7.09  
% 16.14/7.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.14/7.09  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 16.14/7.09  
% 16.14/7.09  %Foreground sorts:
% 16.14/7.09  
% 16.14/7.09  
% 16.14/7.09  %Background operators:
% 16.14/7.09  
% 16.14/7.09  
% 16.14/7.09  %Foreground operators:
% 16.14/7.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.14/7.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.14/7.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.14/7.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.14/7.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.14/7.09  tff('#skF_5', type, '#skF_5': $i).
% 16.14/7.09  tff('#skF_6', type, '#skF_6': $i).
% 16.14/7.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.14/7.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.14/7.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.14/7.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.14/7.09  tff('#skF_4', type, '#skF_4': $i).
% 16.14/7.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.14/7.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.14/7.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.14/7.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.14/7.09  
% 16.14/7.10  tff(f_75, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 16.14/7.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.14/7.10  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.14/7.10  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.14/7.10  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 16.14/7.10  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 16.14/7.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.14/7.10  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.14/7.10  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.14/7.10  tff(f_62, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 16.14/7.10  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 16.14/7.10  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.14/7.10  tff(c_64, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.14/7.10  tff(c_42, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.14/7.10  tff(c_79, plain, (![A_35, B_34]: (r1_tarski(A_35, k2_xboole_0(B_34, A_35)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_42])).
% 16.14/7.10  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.14/7.10  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.14/7.10  tff(c_210, plain, (![A_64, B_65, C_66]: (r1_tarski(k4_xboole_0(A_64, B_65), C_66) | ~r1_tarski(A_64, k2_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.14/7.10  tff(c_222, plain, (![A_67, C_68]: (r1_tarski(A_67, C_68) | ~r1_tarski(A_67, k2_xboole_0(k1_xboole_0, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_210])).
% 16.14/7.10  tff(c_259, plain, (![C_69]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_69), C_69))), inference(resolution, [status(thm)], [c_32, c_222])).
% 16.14/7.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.14/7.10  tff(c_119, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.14/7.10  tff(c_182, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(k2_xboole_0(A_56, B_57), A_56))), inference(resolution, [status(thm)], [c_42, c_119])).
% 16.14/7.10  tff(c_188, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=B_2 | ~r1_tarski(k2_xboole_0(A_1, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 16.14/7.10  tff(c_294, plain, (![C_69]: (k2_xboole_0(C_69, k1_xboole_0)=C_69)), inference(resolution, [status(thm)], [c_259, c_188])).
% 16.14/7.10  tff(c_38, plain, (![A_18, B_19, C_20]: (r1_tarski(k4_xboole_0(A_18, B_19), C_20) | ~r1_tarski(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.14/7.10  tff(c_48, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.14/7.10  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.14/7.10  tff(c_178, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.14/7.10  tff(c_2300, plain, (![A_166, B_167, B_168]: (r2_hidden('#skF_1'(A_166, B_167), B_168) | ~r1_tarski(A_166, B_168) | r1_tarski(A_166, B_167))), inference(resolution, [status(thm)], [c_8, c_178])).
% 16.14/7.10  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.14/7.10  tff(c_39913, plain, (![A_833, B_834, B_835, B_836]: (r2_hidden('#skF_1'(A_833, B_834), B_835) | ~r1_tarski(B_836, B_835) | ~r1_tarski(A_833, B_836) | r1_tarski(A_833, B_834))), inference(resolution, [status(thm)], [c_2300, c_4])).
% 16.14/7.10  tff(c_40112, plain, (![A_837, B_838]: (r2_hidden('#skF_1'(A_837, B_838), '#skF_5') | ~r1_tarski(A_837, '#skF_4') | r1_tarski(A_837, B_838))), inference(resolution, [status(thm)], [c_48, c_39913])).
% 16.14/7.10  tff(c_151, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.14/7.10  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.14/7.10  tff(c_167, plain, (![A_8, B_9, B_49]: (~r2_hidden('#skF_1'(k4_xboole_0(A_8, B_9), B_49), B_9) | r1_tarski(k4_xboole_0(A_8, B_9), B_49))), inference(resolution, [status(thm)], [c_151, c_12])).
% 16.14/7.10  tff(c_40262, plain, (![A_842, B_843]: (~r1_tarski(k4_xboole_0(A_842, '#skF_5'), '#skF_4') | r1_tarski(k4_xboole_0(A_842, '#skF_5'), B_843))), inference(resolution, [status(thm)], [c_40112, c_167])).
% 16.14/7.10  tff(c_40299, plain, (![A_18, B_843]: (r1_tarski(k4_xboole_0(A_18, '#skF_5'), B_843) | ~r1_tarski(A_18, k2_xboole_0('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_38, c_40262])).
% 16.14/7.10  tff(c_40322, plain, (![A_844, B_845]: (r1_tarski(k4_xboole_0(A_844, '#skF_5'), B_845) | ~r1_tarski(A_844, k2_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40299])).
% 16.14/7.10  tff(c_34, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.14/7.10  tff(c_136, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_119])).
% 16.14/7.10  tff(c_40430, plain, (![A_846]: (k4_xboole_0(A_846, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_846, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_40322, c_136])).
% 16.14/7.10  tff(c_40526, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_40430])).
% 16.14/7.10  tff(c_358, plain, (![A_71, B_72, C_73]: (r1_tarski(A_71, k2_xboole_0(B_72, C_73)) | ~r1_tarski(k4_xboole_0(A_71, B_72), C_73))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.14/7.10  tff(c_517, plain, (![A_81, B_82]: (r1_tarski(A_81, k2_xboole_0(B_82, k4_xboole_0(A_81, B_82))))), inference(resolution, [status(thm)], [c_32, c_358])).
% 16.14/7.10  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.14/7.10  tff(c_532, plain, (![B_82, A_81]: (k2_xboole_0(B_82, k4_xboole_0(A_81, B_82))=A_81 | ~r1_tarski(k2_xboole_0(B_82, k4_xboole_0(A_81, B_82)), A_81))), inference(resolution, [status(thm)], [c_517, c_28])).
% 16.14/7.10  tff(c_40591, plain, (k2_xboole_0('#skF_5', k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5') | ~r1_tarski(k2_xboole_0('#skF_5', k1_xboole_0), k2_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40526, c_532])).
% 16.14/7.10  tff(c_40807, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_294, c_294, c_40526, c_40591])).
% 16.14/7.10  tff(c_474, plain, (![C_78, A_79, B_80]: (k2_xboole_0(k9_relat_1(C_78, A_79), k9_relat_1(C_78, B_80))=k9_relat_1(C_78, k2_xboole_0(A_79, B_80)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.14/7.10  tff(c_501, plain, (![C_78, A_79, B_80]: (r1_tarski(k9_relat_1(C_78, A_79), k9_relat_1(C_78, k2_xboole_0(A_79, B_80))) | ~v1_relat_1(C_78))), inference(superposition, [status(thm), theory('equality')], [c_474, c_42])).
% 16.14/7.10  tff(c_43960, plain, (![C_887]: (r1_tarski(k9_relat_1(C_887, '#skF_4'), k9_relat_1(C_887, '#skF_5')) | ~v1_relat_1(C_887))), inference(superposition, [status(thm), theory('equality')], [c_40807, c_501])).
% 16.14/7.10  tff(c_46, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.14/7.10  tff(c_43970, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_43960, c_46])).
% 16.14/7.10  tff(c_43977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_43970])).
% 16.14/7.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.14/7.10  
% 16.14/7.10  Inference rules
% 16.14/7.10  ----------------------
% 16.14/7.10  #Ref     : 0
% 16.14/7.10  #Sup     : 10911
% 16.14/7.10  #Fact    : 2
% 16.14/7.10  #Define  : 0
% 16.14/7.10  #Split   : 5
% 16.14/7.10  #Chain   : 0
% 16.14/7.10  #Close   : 0
% 16.14/7.10  
% 16.14/7.10  Ordering : KBO
% 16.14/7.10  
% 16.14/7.10  Simplification rules
% 16.14/7.10  ----------------------
% 16.14/7.10  #Subsume      : 2755
% 16.14/7.10  #Demod        : 12761
% 16.14/7.10  #Tautology    : 5089
% 16.14/7.10  #SimpNegUnit  : 132
% 16.14/7.10  #BackRed      : 167
% 16.14/7.10  
% 16.14/7.10  #Partial instantiations: 0
% 16.14/7.10  #Strategies tried      : 1
% 16.14/7.10  
% 16.14/7.10  Timing (in seconds)
% 16.14/7.10  ----------------------
% 16.33/7.11  Preprocessing        : 0.29
% 16.33/7.11  Parsing              : 0.15
% 16.33/7.11  CNF conversion       : 0.02
% 16.33/7.11  Main loop            : 6.05
% 16.33/7.11  Inferencing          : 1.05
% 16.33/7.11  Reduction            : 3.20
% 16.33/7.11  Demodulation         : 2.79
% 16.33/7.11  BG Simplification    : 0.11
% 16.33/7.11  Subsumption          : 1.37
% 16.33/7.11  Abstraction          : 0.19
% 16.33/7.11  MUC search           : 0.00
% 16.33/7.11  Cooper               : 0.00
% 16.33/7.11  Total                : 6.37
% 16.33/7.11  Index Insertion      : 0.00
% 16.33/7.11  Index Deletion       : 0.00
% 16.33/7.11  Index Matching       : 0.00
% 16.33/7.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
