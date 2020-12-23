%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 177 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 416 expanded)
%              Number of equality atoms :   65 ( 339 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(c_36,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_71,plain,(
    k1_tarski('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_24])).

tff(c_484,plain,(
    ! [B_69,A_70] :
      ( k1_tarski(B_69) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_494,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76,c_484])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_71,c_494])).

tff(c_508,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_10,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_708,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,k2_xboole_0(C_87,B_88))
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_716,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k1_tarski('#skF_2'))
      | ~ r1_tarski(A_86,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_708])).

tff(c_509,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( k1_tarski(B_24) = A_23
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_tarski(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_933,plain,(
    ! [B_112,A_113] :
      ( k1_tarski(B_112) = A_113
      | A_113 = '#skF_3'
      | ~ r1_tarski(A_113,k1_tarski(B_112)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_28])).

tff(c_954,plain,(
    ! [A_114] :
      ( k1_tarski('#skF_2') = A_114
      | A_114 = '#skF_3'
      | ~ r1_tarski(A_114,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_716,c_933])).

tff(c_962,plain,
    ( k1_tarski('#skF_2') = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_954])).

tff(c_969,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_962])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ! [A_31,B_32] : r1_xboole_0(k4_xboole_0(A_31,B_32),B_32) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_510,plain,(
    ! [A_16] : r1_xboole_0('#skF_3',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_69])).

tff(c_612,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_513,plain,(
    ! [A_16] : k4_xboole_0('#skF_3',A_16) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_509,c_20])).

tff(c_622,plain,(
    ! [B_82] : k3_xboole_0('#skF_3',B_82) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_513])).

tff(c_804,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,k3_xboole_0(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_810,plain,(
    ! [B_82,C_101] :
      ( ~ r1_xboole_0('#skF_3',B_82)
      | ~ r2_hidden(C_101,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_804])).

tff(c_812,plain,(
    ! [C_101] : ~ r2_hidden(C_101,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_810])).

tff(c_814,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(B_103,A_104)
      | k3_xboole_0(A_104,k1_tarski(B_103)) != k1_tarski(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_822,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,'#skF_3')
      | k1_tarski(B_103) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_814])).

tff(c_823,plain,(
    ! [B_103] : k1_tarski(B_103) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_822])).

tff(c_975,plain,(
    ! [B_103] : k1_tarski(B_103) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_823])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_511,plain,(
    ! [A_11] : k2_xboole_0(A_11,'#skF_3') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_14])).

tff(c_986,plain,(
    ! [A_11] : k2_xboole_0(A_11,'#skF_4') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_511])).

tff(c_988,plain,(
    k2_xboole_0('#skF_4','#skF_4') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_40])).

tff(c_1022,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_988])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_1022])).

tff(c_1025,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1026,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k1_tarski('#skF_2') != '#skF_4'
    | k1_tarski('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1045,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1026,c_38])).

tff(c_1033,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_40])).

tff(c_1099,plain,(
    ! [A_124,C_125,B_126] :
      ( r1_tarski(A_124,k2_xboole_0(C_125,B_126))
      | ~ r1_tarski(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1102,plain,(
    ! [A_124] :
      ( r1_tarski(A_124,'#skF_3')
      | ~ r1_tarski(A_124,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_1099])).

tff(c_1433,plain,(
    ! [B_156,A_157] :
      ( k1_tarski(B_156) = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,k1_tarski(B_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1440,plain,(
    ! [A_157] :
      ( k1_tarski('#skF_2') = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_1433])).

tff(c_1454,plain,(
    ! [A_158] :
      ( A_158 = '#skF_3'
      | k1_xboole_0 = A_158
      | ~ r1_tarski(A_158,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1440])).

tff(c_1475,plain,(
    ! [A_159] :
      ( A_159 = '#skF_3'
      | k1_xboole_0 = A_159
      | ~ r1_tarski(A_159,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1102,c_1454])).

tff(c_1483,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_1475])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1025,c_1045,c_1483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n023.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:39:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.47  
% 3.09/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.09/1.47  
% 3.09/1.47  %Foreground sorts:
% 3.09/1.47  
% 3.09/1.47  
% 3.09/1.47  %Background operators:
% 3.09/1.47  
% 3.09/1.47  
% 3.09/1.47  %Foreground operators:
% 3.09/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.47  
% 3.17/1.48  tff(f_90, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.17/1.48  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.17/1.48  tff(f_71, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.17/1.48  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.48  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.17/1.48  tff(f_57, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.17/1.48  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.17/1.48  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.17/1.48  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.17/1.48  tff(f_65, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 3.17/1.48  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.17/1.48  tff(c_36, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.17/1.48  tff(c_72, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 3.17/1.48  tff(c_34, plain, (k1_xboole_0!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.17/1.48  tff(c_71, plain, (k1_tarski('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 3.17/1.48  tff(c_40, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.17/1.48  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.17/1.48  tff(c_76, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_24])).
% 3.17/1.48  tff(c_484, plain, (![B_69, A_70]: (k1_tarski(B_69)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.17/1.48  tff(c_494, plain, (k1_tarski('#skF_2')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_76, c_484])).
% 3.17/1.48  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_71, c_494])).
% 3.17/1.48  tff(c_508, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 3.17/1.48  tff(c_10, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.17/1.48  tff(c_708, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, k2_xboole_0(C_87, B_88)) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.48  tff(c_716, plain, (![A_86]: (r1_tarski(A_86, k1_tarski('#skF_2')) | ~r1_tarski(A_86, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_708])).
% 3.17/1.48  tff(c_509, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.17/1.48  tff(c_28, plain, (![B_24, A_23]: (k1_tarski(B_24)=A_23 | k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_tarski(B_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.17/1.48  tff(c_933, plain, (![B_112, A_113]: (k1_tarski(B_112)=A_113 | A_113='#skF_3' | ~r1_tarski(A_113, k1_tarski(B_112)))), inference(demodulation, [status(thm), theory('equality')], [c_509, c_28])).
% 3.17/1.48  tff(c_954, plain, (![A_114]: (k1_tarski('#skF_2')=A_114 | A_114='#skF_3' | ~r1_tarski(A_114, '#skF_4'))), inference(resolution, [status(thm)], [c_716, c_933])).
% 3.17/1.48  tff(c_962, plain, (k1_tarski('#skF_2')='#skF_4' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_10, c_954])).
% 3.17/1.48  tff(c_969, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_508, c_962])).
% 3.17/1.48  tff(c_20, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.48  tff(c_66, plain, (![A_31, B_32]: (r1_xboole_0(k4_xboole_0(A_31, B_32), B_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.17/1.48  tff(c_69, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_66])).
% 3.17/1.48  tff(c_510, plain, (![A_16]: (r1_xboole_0('#skF_3', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_509, c_69])).
% 3.17/1.48  tff(c_612, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.48  tff(c_513, plain, (![A_16]: (k4_xboole_0('#skF_3', A_16)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_509, c_20])).
% 3.17/1.48  tff(c_622, plain, (![B_82]: (k3_xboole_0('#skF_3', B_82)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_612, c_513])).
% 3.17/1.48  tff(c_804, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, k3_xboole_0(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.48  tff(c_810, plain, (![B_82, C_101]: (~r1_xboole_0('#skF_3', B_82) | ~r2_hidden(C_101, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_622, c_804])).
% 3.17/1.48  tff(c_812, plain, (![C_101]: (~r2_hidden(C_101, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_810])).
% 3.17/1.48  tff(c_814, plain, (![B_103, A_104]: (r2_hidden(B_103, A_104) | k3_xboole_0(A_104, k1_tarski(B_103))!=k1_tarski(B_103))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.48  tff(c_822, plain, (![B_103]: (r2_hidden(B_103, '#skF_3') | k1_tarski(B_103)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_622, c_814])).
% 3.17/1.48  tff(c_823, plain, (![B_103]: (k1_tarski(B_103)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_812, c_822])).
% 3.17/1.48  tff(c_975, plain, (![B_103]: (k1_tarski(B_103)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_823])).
% 3.17/1.48  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.17/1.48  tff(c_511, plain, (![A_11]: (k2_xboole_0(A_11, '#skF_3')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_509, c_14])).
% 3.17/1.48  tff(c_986, plain, (![A_11]: (k2_xboole_0(A_11, '#skF_4')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_969, c_511])).
% 3.17/1.48  tff(c_988, plain, (k2_xboole_0('#skF_4', '#skF_4')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_40])).
% 3.17/1.48  tff(c_1022, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_986, c_988])).
% 3.17/1.48  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_975, c_1022])).
% 3.17/1.48  tff(c_1025, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 3.17/1.48  tff(c_1026, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.17/1.48  tff(c_38, plain, (k1_tarski('#skF_2')!='#skF_4' | k1_tarski('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.17/1.48  tff(c_1045, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1026, c_38])).
% 3.17/1.48  tff(c_1033, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_40])).
% 3.17/1.48  tff(c_1099, plain, (![A_124, C_125, B_126]: (r1_tarski(A_124, k2_xboole_0(C_125, B_126)) | ~r1_tarski(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.48  tff(c_1102, plain, (![A_124]: (r1_tarski(A_124, '#skF_3') | ~r1_tarski(A_124, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_1099])).
% 3.17/1.48  tff(c_1433, plain, (![B_156, A_157]: (k1_tarski(B_156)=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, k1_tarski(B_156)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.17/1.48  tff(c_1440, plain, (![A_157]: (k1_tarski('#skF_2')=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1026, c_1433])).
% 3.17/1.48  tff(c_1454, plain, (![A_158]: (A_158='#skF_3' | k1_xboole_0=A_158 | ~r1_tarski(A_158, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1440])).
% 3.17/1.48  tff(c_1475, plain, (![A_159]: (A_159='#skF_3' | k1_xboole_0=A_159 | ~r1_tarski(A_159, '#skF_4'))), inference(resolution, [status(thm)], [c_1102, c_1454])).
% 3.17/1.48  tff(c_1483, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_1475])).
% 3.17/1.48  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1025, c_1045, c_1483])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 330
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 4
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 14
% 3.17/1.48  #Demod        : 187
% 3.17/1.48  #Tautology    : 226
% 3.17/1.48  #SimpNegUnit  : 17
% 3.17/1.48  #BackRed      : 30
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.49  Preprocessing        : 0.31
% 3.17/1.49  Parsing              : 0.17
% 3.17/1.49  CNF conversion       : 0.02
% 3.17/1.49  Main loop            : 0.39
% 3.17/1.49  Inferencing          : 0.15
% 3.17/1.49  Reduction            : 0.13
% 3.17/1.49  Demodulation         : 0.09
% 3.17/1.49  BG Simplification    : 0.02
% 3.17/1.49  Subsumption          : 0.06
% 3.17/1.49  Abstraction          : 0.02
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.74
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
