%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:03 EST 2020

% Result     : Theorem 16.83s
% Output     : CNFRefutation 16.83s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 160 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 289 expanded)
%              Number of equality atoms :   20 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_75,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_40])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_317,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski(k4_xboole_0(A_79,B_80),C_81)
      | ~ r1_tarski(A_79,k2_xboole_0(B_80,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_333,plain,(
    ! [A_82,C_83] :
      ( r1_tarski(A_82,C_83)
      | ~ r1_tarski(A_82,k2_xboole_0(k1_xboole_0,C_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_317])).

tff(c_385,plain,(
    ! [C_84] : r1_tarski(k2_xboole_0(k1_xboole_0,C_84),C_84) ),
    inference(resolution,[status(thm)],[c_32,c_333])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_200,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(k2_xboole_0(A_64,B_65),A_64) ) ),
    inference(resolution,[status(thm)],[c_40,c_155])).

tff(c_203,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(k2_xboole_0(B_2,A_1),A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_415,plain,(
    ! [C_84] : k2_xboole_0(C_84,k1_xboole_0) = C_84 ),
    inference(resolution,[status(thm)],[c_385,c_203])).

tff(c_36,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(k4_xboole_0(A_17,B_18),C_19)
      | ~ r1_tarski(A_17,k2_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_178,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2196,plain,(
    ! [A_175,B_176,B_177] :
      ( r2_hidden('#skF_1'(A_175,B_176),B_177)
      | ~ r1_tarski(A_175,B_177)
      | r1_tarski(A_175,B_176) ) ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42814,plain,(
    ! [A_889,B_890,B_891,B_892] :
      ( r2_hidden('#skF_1'(A_889,B_890),B_891)
      | ~ r1_tarski(B_892,B_891)
      | ~ r1_tarski(A_889,B_892)
      | r1_tarski(A_889,B_890) ) ),
    inference(resolution,[status(thm)],[c_2196,c_4])).

tff(c_43046,plain,(
    ! [A_893,B_894] :
      ( r2_hidden('#skF_1'(A_893,B_894),'#skF_5')
      | ~ r1_tarski(A_893,'#skF_4')
      | r1_tarski(A_893,B_894) ) ),
    inference(resolution,[status(thm)],[c_50,c_42814])).

tff(c_134,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,(
    ! [A_8,B_9,B_54] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_8,B_9),B_54),B_9)
      | r1_tarski(k4_xboole_0(A_8,B_9),B_54) ) ),
    inference(resolution,[status(thm)],[c_134,c_12])).

tff(c_43077,plain,(
    ! [A_895,B_896] :
      ( ~ r1_tarski(k4_xboole_0(A_895,'#skF_5'),'#skF_4')
      | r1_tarski(k4_xboole_0(A_895,'#skF_5'),B_896) ) ),
    inference(resolution,[status(thm)],[c_43046,c_154])).

tff(c_43117,plain,(
    ! [A_17,B_896] :
      ( r1_tarski(k4_xboole_0(A_17,'#skF_5'),B_896)
      | ~ r1_tarski(A_17,k2_xboole_0('#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_43077])).

tff(c_43141,plain,(
    ! [A_897,B_898] :
      ( r1_tarski(k4_xboole_0(A_897,'#skF_5'),B_898)
      | ~ r1_tarski(A_897,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_43117])).

tff(c_124,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_127,plain,(
    ! [D_43,A_16] :
      ( ~ r2_hidden(D_43,k1_xboole_0)
      | ~ r2_hidden(D_43,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_124])).

tff(c_172,plain,(
    ! [B_57,A_58] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_57),A_58)
      | r1_tarski(k1_xboole_0,B_57) ) ),
    inference(resolution,[status(thm)],[c_134,c_127])).

tff(c_183,plain,(
    ! [B_62] : r1_tarski(k1_xboole_0,B_62) ),
    inference(resolution,[status(thm)],[c_8,c_172])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_186,plain,(
    ! [B_62] :
      ( k1_xboole_0 = B_62
      | ~ r1_tarski(B_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_183,c_28])).

tff(c_43263,plain,(
    ! [A_899] :
      ( k4_xboole_0(A_899,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_899,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_43141,c_186])).

tff(c_43376,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_43263])).

tff(c_221,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(A_70,k2_xboole_0(B_71,C_72))
      | ~ r1_tarski(k4_xboole_0(A_70,B_71),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_240,plain,(
    ! [A_73,B_74] : r1_tarski(A_73,k2_xboole_0(B_74,k4_xboole_0(A_73,B_74))) ),
    inference(resolution,[status(thm)],[c_32,c_221])).

tff(c_251,plain,(
    ! [B_74,A_73] :
      ( k2_xboole_0(B_74,k4_xboole_0(A_73,B_74)) = A_73
      | ~ r1_tarski(k2_xboole_0(B_74,k4_xboole_0(A_73,B_74)),A_73) ) ),
    inference(resolution,[status(thm)],[c_240,c_28])).

tff(c_43419,plain,
    ( k2_xboole_0('#skF_5',k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_5')) = k2_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski(k2_xboole_0('#skF_5',k1_xboole_0),k2_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43376,c_251])).

tff(c_43633,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_415,c_415,c_43376,c_43419])).

tff(c_571,plain,(
    ! [C_90,A_91,B_92] :
      ( k2_xboole_0(k9_relat_1(C_90,A_91),k9_relat_1(C_90,B_92)) = k9_relat_1(C_90,k2_xboole_0(A_91,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_595,plain,(
    ! [C_90,A_91,B_92] :
      ( r1_tarski(k9_relat_1(C_90,A_91),k9_relat_1(C_90,k2_xboole_0(A_91,B_92)))
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_40])).

tff(c_45272,plain,(
    ! [C_923] :
      ( r1_tarski(k9_relat_1(C_923,'#skF_4'),k9_relat_1(C_923,'#skF_5'))
      | ~ v1_relat_1(C_923) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43633,c_595])).

tff(c_48,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_45282,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_45272,c_48])).

tff(c_45289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_45282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.83/7.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.83/7.44  
% 16.83/7.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.83/7.44  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 16.83/7.44  
% 16.83/7.44  %Foreground sorts:
% 16.83/7.44  
% 16.83/7.44  
% 16.83/7.44  %Background operators:
% 16.83/7.44  
% 16.83/7.44  
% 16.83/7.44  %Foreground operators:
% 16.83/7.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.83/7.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.83/7.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.83/7.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.83/7.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.83/7.44  tff('#skF_5', type, '#skF_5': $i).
% 16.83/7.44  tff('#skF_6', type, '#skF_6': $i).
% 16.83/7.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.83/7.44  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 16.83/7.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.83/7.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.83/7.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.83/7.44  tff('#skF_4', type, '#skF_4': $i).
% 16.83/7.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.83/7.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.83/7.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.83/7.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.83/7.44  
% 16.83/7.46  tff(f_79, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 16.83/7.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.83/7.46  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.83/7.46  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.83/7.46  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 16.83/7.46  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 16.83/7.46  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.83/7.46  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.83/7.46  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 16.83/7.46  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 16.83/7.46  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.83/7.46  tff(c_75, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.83/7.46  tff(c_40, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.83/7.46  tff(c_90, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_40])).
% 16.83/7.46  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.83/7.46  tff(c_34, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.83/7.46  tff(c_317, plain, (![A_79, B_80, C_81]: (r1_tarski(k4_xboole_0(A_79, B_80), C_81) | ~r1_tarski(A_79, k2_xboole_0(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.83/7.46  tff(c_333, plain, (![A_82, C_83]: (r1_tarski(A_82, C_83) | ~r1_tarski(A_82, k2_xboole_0(k1_xboole_0, C_83)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_317])).
% 16.83/7.46  tff(c_385, plain, (![C_84]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_84), C_84))), inference(resolution, [status(thm)], [c_32, c_333])).
% 16.83/7.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.83/7.46  tff(c_155, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.83/7.46  tff(c_200, plain, (![A_64, B_65]: (k2_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(k2_xboole_0(A_64, B_65), A_64))), inference(resolution, [status(thm)], [c_40, c_155])).
% 16.83/7.46  tff(c_203, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(k2_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_200])).
% 16.83/7.46  tff(c_415, plain, (![C_84]: (k2_xboole_0(C_84, k1_xboole_0)=C_84)), inference(resolution, [status(thm)], [c_385, c_203])).
% 16.83/7.46  tff(c_36, plain, (![A_17, B_18, C_19]: (r1_tarski(k4_xboole_0(A_17, B_18), C_19) | ~r1_tarski(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.83/7.46  tff(c_50, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.83/7.46  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.83/7.46  tff(c_178, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.83/7.46  tff(c_2196, plain, (![A_175, B_176, B_177]: (r2_hidden('#skF_1'(A_175, B_176), B_177) | ~r1_tarski(A_175, B_177) | r1_tarski(A_175, B_176))), inference(resolution, [status(thm)], [c_8, c_178])).
% 16.83/7.46  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.83/7.46  tff(c_42814, plain, (![A_889, B_890, B_891, B_892]: (r2_hidden('#skF_1'(A_889, B_890), B_891) | ~r1_tarski(B_892, B_891) | ~r1_tarski(A_889, B_892) | r1_tarski(A_889, B_890))), inference(resolution, [status(thm)], [c_2196, c_4])).
% 16.83/7.46  tff(c_43046, plain, (![A_893, B_894]: (r2_hidden('#skF_1'(A_893, B_894), '#skF_5') | ~r1_tarski(A_893, '#skF_4') | r1_tarski(A_893, B_894))), inference(resolution, [status(thm)], [c_50, c_42814])).
% 16.83/7.46  tff(c_134, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.83/7.46  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.83/7.46  tff(c_154, plain, (![A_8, B_9, B_54]: (~r2_hidden('#skF_1'(k4_xboole_0(A_8, B_9), B_54), B_9) | r1_tarski(k4_xboole_0(A_8, B_9), B_54))), inference(resolution, [status(thm)], [c_134, c_12])).
% 16.83/7.46  tff(c_43077, plain, (![A_895, B_896]: (~r1_tarski(k4_xboole_0(A_895, '#skF_5'), '#skF_4') | r1_tarski(k4_xboole_0(A_895, '#skF_5'), B_896))), inference(resolution, [status(thm)], [c_43046, c_154])).
% 16.83/7.46  tff(c_43117, plain, (![A_17, B_896]: (r1_tarski(k4_xboole_0(A_17, '#skF_5'), B_896) | ~r1_tarski(A_17, k2_xboole_0('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_36, c_43077])).
% 16.83/7.46  tff(c_43141, plain, (![A_897, B_898]: (r1_tarski(k4_xboole_0(A_897, '#skF_5'), B_898) | ~r1_tarski(A_897, k2_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_43117])).
% 16.83/7.46  tff(c_124, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.83/7.46  tff(c_127, plain, (![D_43, A_16]: (~r2_hidden(D_43, k1_xboole_0) | ~r2_hidden(D_43, A_16))), inference(superposition, [status(thm), theory('equality')], [c_34, c_124])).
% 16.83/7.46  tff(c_172, plain, (![B_57, A_58]: (~r2_hidden('#skF_1'(k1_xboole_0, B_57), A_58) | r1_tarski(k1_xboole_0, B_57))), inference(resolution, [status(thm)], [c_134, c_127])).
% 16.83/7.46  tff(c_183, plain, (![B_62]: (r1_tarski(k1_xboole_0, B_62))), inference(resolution, [status(thm)], [c_8, c_172])).
% 16.83/7.46  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.83/7.46  tff(c_186, plain, (![B_62]: (k1_xboole_0=B_62 | ~r1_tarski(B_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_183, c_28])).
% 16.83/7.46  tff(c_43263, plain, (![A_899]: (k4_xboole_0(A_899, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_899, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_43141, c_186])).
% 16.83/7.46  tff(c_43376, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_43263])).
% 16.83/7.46  tff(c_221, plain, (![A_70, B_71, C_72]: (r1_tarski(A_70, k2_xboole_0(B_71, C_72)) | ~r1_tarski(k4_xboole_0(A_70, B_71), C_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.83/7.46  tff(c_240, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_xboole_0(B_74, k4_xboole_0(A_73, B_74))))), inference(resolution, [status(thm)], [c_32, c_221])).
% 16.83/7.46  tff(c_251, plain, (![B_74, A_73]: (k2_xboole_0(B_74, k4_xboole_0(A_73, B_74))=A_73 | ~r1_tarski(k2_xboole_0(B_74, k4_xboole_0(A_73, B_74)), A_73))), inference(resolution, [status(thm)], [c_240, c_28])).
% 16.83/7.46  tff(c_43419, plain, (k2_xboole_0('#skF_5', k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5') | ~r1_tarski(k2_xboole_0('#skF_5', k1_xboole_0), k2_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_43376, c_251])).
% 16.83/7.46  tff(c_43633, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_415, c_415, c_43376, c_43419])).
% 16.83/7.46  tff(c_571, plain, (![C_90, A_91, B_92]: (k2_xboole_0(k9_relat_1(C_90, A_91), k9_relat_1(C_90, B_92))=k9_relat_1(C_90, k2_xboole_0(A_91, B_92)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.83/7.46  tff(c_595, plain, (![C_90, A_91, B_92]: (r1_tarski(k9_relat_1(C_90, A_91), k9_relat_1(C_90, k2_xboole_0(A_91, B_92))) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_571, c_40])).
% 16.83/7.46  tff(c_45272, plain, (![C_923]: (r1_tarski(k9_relat_1(C_923, '#skF_4'), k9_relat_1(C_923, '#skF_5')) | ~v1_relat_1(C_923))), inference(superposition, [status(thm), theory('equality')], [c_43633, c_595])).
% 16.83/7.46  tff(c_48, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.83/7.46  tff(c_45282, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_45272, c_48])).
% 16.83/7.46  tff(c_45289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_45282])).
% 16.83/7.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.83/7.46  
% 16.83/7.46  Inference rules
% 16.83/7.46  ----------------------
% 16.83/7.46  #Ref     : 0
% 16.83/7.46  #Sup     : 11362
% 16.83/7.46  #Fact    : 2
% 16.83/7.46  #Define  : 0
% 16.83/7.46  #Split   : 2
% 16.83/7.46  #Chain   : 0
% 16.83/7.46  #Close   : 0
% 16.83/7.46  
% 16.83/7.46  Ordering : KBO
% 16.83/7.46  
% 16.83/7.46  Simplification rules
% 16.83/7.46  ----------------------
% 16.83/7.46  #Subsume      : 2724
% 16.83/7.46  #Demod        : 11755
% 16.83/7.46  #Tautology    : 5338
% 16.83/7.46  #SimpNegUnit  : 91
% 16.83/7.46  #BackRed      : 94
% 16.83/7.46  
% 16.83/7.46  #Partial instantiations: 0
% 16.83/7.46  #Strategies tried      : 1
% 16.83/7.46  
% 16.83/7.46  Timing (in seconds)
% 16.83/7.46  ----------------------
% 16.83/7.46  Preprocessing        : 0.32
% 16.83/7.46  Parsing              : 0.17
% 16.83/7.46  CNF conversion       : 0.02
% 16.83/7.46  Main loop            : 6.33
% 16.83/7.46  Inferencing          : 1.07
% 16.83/7.46  Reduction            : 3.31
% 16.83/7.46  Demodulation         : 2.89
% 16.83/7.46  BG Simplification    : 0.12
% 16.83/7.46  Subsumption          : 1.49
% 16.83/7.46  Abstraction          : 0.18
% 16.83/7.46  MUC search           : 0.00
% 16.83/7.46  Cooper               : 0.00
% 16.83/7.46  Total                : 6.68
% 16.83/7.46  Index Insertion      : 0.00
% 16.83/7.46  Index Deletion       : 0.00
% 16.83/7.46  Index Matching       : 0.00
% 16.83/7.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
