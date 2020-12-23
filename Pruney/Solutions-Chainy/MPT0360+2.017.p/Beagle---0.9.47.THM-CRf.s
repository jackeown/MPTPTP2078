%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 10.67s
% Output     : CNFRefutation 10.67s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 198 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 274 expanded)
%              Number of equality atoms :   49 ( 148 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_68,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_97,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_98,plain,(
    ! [B_39,A_40] : k5_xboole_0(B_39,A_40) = k5_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_114,plain,(
    ! [A_40] : k5_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_30])).

tff(c_34,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_339,plain,(
    ! [A_70,B_71,C_72] : k5_xboole_0(k5_xboole_0(A_70,B_71),C_72) = k5_xboole_0(A_70,k5_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_403,plain,(
    ! [A_22,C_72] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_72)) = k5_xboole_0(k1_xboole_0,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_339])).

tff(c_416,plain,(
    ! [A_22,C_72] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_72)) = C_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_403])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_201,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_66,c_201])).

tff(c_1086,plain,(
    ! [A_99,B_100] : k5_xboole_0(k5_xboole_0(A_99,B_100),k2_xboole_0(A_99,B_100)) = k3_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1171,plain,(
    k5_xboole_0(k5_xboole_0('#skF_5','#skF_6'),'#skF_6') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_1086])).

tff(c_1203,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_2,c_2,c_1171])).

tff(c_64,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_417,plain,(
    ! [A_73,C_74] : k5_xboole_0(A_73,k5_xboole_0(A_73,C_74)) = C_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_403])).

tff(c_460,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_417])).

tff(c_482,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k5_xboole_0(B_76,A_75)) = B_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_417])).

tff(c_509,plain,(
    ! [B_2,A_1] : k5_xboole_0(k5_xboole_0(B_2,A_1),B_2) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_482])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_289,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(B_62,A_63)
      | ~ m1_subset_1(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_293,plain,(
    ! [B_62,A_25] :
      ( r1_tarski(B_62,A_25)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_289,c_38])).

tff(c_297,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_293])).

tff(c_306,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_297])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(A_14,'#skF_1'(A_14,B_15,C_16))
      | k2_xboole_0(A_14,C_16) = B_15
      | ~ r1_tarski(C_16,B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2369,plain,(
    ! [B_148,A_149,C_150] :
      ( ~ r1_tarski(B_148,'#skF_1'(A_149,B_148,C_150))
      | k2_xboole_0(A_149,C_150) = B_148
      | ~ r1_tarski(C_150,B_148)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2373,plain,(
    ! [B_15,C_16] :
      ( k2_xboole_0(B_15,C_16) = B_15
      | ~ r1_tarski(C_16,B_15)
      | ~ r1_tarski(B_15,B_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_2369])).

tff(c_2389,plain,(
    ! [B_151,C_152] :
      ( k2_xboole_0(B_151,C_152) = B_151
      | ~ r1_tarski(C_152,B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2373])).

tff(c_2455,plain,(
    k2_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_306,c_2389])).

tff(c_36,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k2_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2479,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_6'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_36])).

tff(c_2488,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_2479])).

tff(c_772,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_785,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_772])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1960,plain,(
    ! [A_138,B_139] : k5_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = k3_xboole_0(A_138,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_417])).

tff(c_2034,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_6')) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_1960])).

tff(c_2120,plain,(
    k5_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_6')) = k3_subset_1('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2034,c_416])).

tff(c_3811,plain,(
    k5_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2120])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_xboole_0(A_9,k3_xboole_0(B_10,C_11))
      | ~ r1_tarski(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2541,plain,(
    ! [A_9] :
      ( r1_xboole_0(A_9,'#skF_6')
      | ~ r1_tarski(A_9,k5_xboole_0('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_18])).

tff(c_18426,plain,(
    ! [A_270] :
      ( r1_xboole_0(A_270,'#skF_6')
      | ~ r1_tarski(A_270,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3811,c_2541])).

tff(c_18467,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_18426])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18476,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18467,c_4])).

tff(c_18478,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_18476])).

tff(c_18480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_18478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.67/4.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.67/4.28  
% 10.67/4.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.67/4.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 10.67/4.29  
% 10.67/4.29  %Foreground sorts:
% 10.67/4.29  
% 10.67/4.29  
% 10.67/4.29  %Background operators:
% 10.67/4.29  
% 10.67/4.29  
% 10.67/4.29  %Foreground operators:
% 10.67/4.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.67/4.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.67/4.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.67/4.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.67/4.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.67/4.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.67/4.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.67/4.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.67/4.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.67/4.29  tff('#skF_5', type, '#skF_5': $i).
% 10.67/4.29  tff('#skF_6', type, '#skF_6': $i).
% 10.67/4.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.67/4.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.67/4.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.67/4.29  tff('#skF_4', type, '#skF_4': $i).
% 10.67/4.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.67/4.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.67/4.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.67/4.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.67/4.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.67/4.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.67/4.29  
% 10.67/4.30  tff(f_106, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 10.67/4.30  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.67/4.30  tff(f_64, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.67/4.30  tff(f_68, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.67/4.30  tff(f_66, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.67/4.30  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.67/4.30  tff(f_70, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.67/4.30  tff(f_97, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.67/4.30  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.67/4.30  tff(f_77, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.67/4.30  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.67/4.30  tff(f_62, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 10.67/4.30  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.67/4.30  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.67/4.30  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 10.67/4.30  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.67/4.30  tff(c_62, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.67/4.30  tff(c_98, plain, (![B_39, A_40]: (k5_xboole_0(B_39, A_40)=k5_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.67/4.30  tff(c_30, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.67/4.30  tff(c_114, plain, (![A_40]: (k5_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_98, c_30])).
% 10.67/4.30  tff(c_34, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.67/4.30  tff(c_339, plain, (![A_70, B_71, C_72]: (k5_xboole_0(k5_xboole_0(A_70, B_71), C_72)=k5_xboole_0(A_70, k5_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.67/4.30  tff(c_403, plain, (![A_22, C_72]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_72))=k5_xboole_0(k1_xboole_0, C_72))), inference(superposition, [status(thm), theory('equality')], [c_34, c_339])).
% 10.67/4.30  tff(c_416, plain, (![A_22, C_72]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_72))=C_72)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_403])).
% 10.67/4.30  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.67/4.30  tff(c_66, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.67/4.30  tff(c_201, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.67/4.30  tff(c_213, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_66, c_201])).
% 10.67/4.30  tff(c_1086, plain, (![A_99, B_100]: (k5_xboole_0(k5_xboole_0(A_99, B_100), k2_xboole_0(A_99, B_100))=k3_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.67/4.30  tff(c_1171, plain, (k5_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), '#skF_6')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_213, c_1086])).
% 10.67/4.30  tff(c_1203, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_416, c_2, c_2, c_1171])).
% 10.67/4.30  tff(c_64, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.67/4.30  tff(c_417, plain, (![A_73, C_74]: (k5_xboole_0(A_73, k5_xboole_0(A_73, C_74))=C_74)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_403])).
% 10.67/4.30  tff(c_460, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_417])).
% 10.67/4.30  tff(c_482, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k5_xboole_0(B_76, A_75))=B_76)), inference(superposition, [status(thm), theory('equality')], [c_2, c_417])).
% 10.67/4.30  tff(c_509, plain, (![B_2, A_1]: (k5_xboole_0(k5_xboole_0(B_2, A_1), B_2)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_460, c_482])).
% 10.67/4.30  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.67/4.30  tff(c_60, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.67/4.30  tff(c_289, plain, (![B_62, A_63]: (r2_hidden(B_62, A_63) | ~m1_subset_1(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.67/4.30  tff(c_38, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.67/4.30  tff(c_293, plain, (![B_62, A_25]: (r1_tarski(B_62, A_25) | ~m1_subset_1(B_62, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_289, c_38])).
% 10.67/4.30  tff(c_297, plain, (![B_64, A_65]: (r1_tarski(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)))), inference(negUnitSimplification, [status(thm)], [c_60, c_293])).
% 10.67/4.30  tff(c_306, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_297])).
% 10.67/4.30  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.67/4.30  tff(c_28, plain, (![A_14, B_15, C_16]: (r1_tarski(A_14, '#skF_1'(A_14, B_15, C_16)) | k2_xboole_0(A_14, C_16)=B_15 | ~r1_tarski(C_16, B_15) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.67/4.30  tff(c_2369, plain, (![B_148, A_149, C_150]: (~r1_tarski(B_148, '#skF_1'(A_149, B_148, C_150)) | k2_xboole_0(A_149, C_150)=B_148 | ~r1_tarski(C_150, B_148) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.67/4.30  tff(c_2373, plain, (![B_15, C_16]: (k2_xboole_0(B_15, C_16)=B_15 | ~r1_tarski(C_16, B_15) | ~r1_tarski(B_15, B_15))), inference(resolution, [status(thm)], [c_28, c_2369])).
% 10.67/4.30  tff(c_2389, plain, (![B_151, C_152]: (k2_xboole_0(B_151, C_152)=B_151 | ~r1_tarski(C_152, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2373])).
% 10.67/4.30  tff(c_2455, plain, (k2_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_306, c_2389])).
% 10.67/4.30  tff(c_36, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k2_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.67/4.30  tff(c_2479, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_6'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2455, c_36])).
% 10.67/4.30  tff(c_2488, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_509, c_2479])).
% 10.67/4.30  tff(c_772, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.67/4.30  tff(c_785, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_772])).
% 10.67/4.30  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.67/4.30  tff(c_1960, plain, (![A_138, B_139]: (k5_xboole_0(A_138, k4_xboole_0(A_138, B_139))=k3_xboole_0(A_138, B_139))), inference(superposition, [status(thm), theory('equality')], [c_14, c_417])).
% 10.67/4.30  tff(c_2034, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_6'))=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_785, c_1960])).
% 10.67/4.30  tff(c_2120, plain, (k5_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))=k3_subset_1('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2034, c_416])).
% 10.67/4.30  tff(c_3811, plain, (k5_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2120])).
% 10.67/4.30  tff(c_18, plain, (![A_9, B_10, C_11]: (r1_xboole_0(A_9, k3_xboole_0(B_10, C_11)) | ~r1_tarski(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.67/4.30  tff(c_2541, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_6') | ~r1_tarski(A_9, k5_xboole_0('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2488, c_18])).
% 10.67/4.30  tff(c_18426, plain, (![A_270]: (r1_xboole_0(A_270, '#skF_6') | ~r1_tarski(A_270, k3_subset_1('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3811, c_2541])).
% 10.67/4.30  tff(c_18467, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_18426])).
% 10.67/4.30  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.67/4.30  tff(c_18476, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_18467, c_4])).
% 10.67/4.30  tff(c_18478, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_18476])).
% 10.67/4.30  tff(c_18480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_18478])).
% 10.67/4.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.67/4.30  
% 10.67/4.30  Inference rules
% 10.67/4.30  ----------------------
% 10.67/4.30  #Ref     : 0
% 10.67/4.30  #Sup     : 4911
% 10.67/4.30  #Fact    : 0
% 10.67/4.30  #Define  : 0
% 10.67/4.30  #Split   : 7
% 10.67/4.30  #Chain   : 0
% 10.67/4.30  #Close   : 0
% 10.67/4.30  
% 10.67/4.30  Ordering : KBO
% 10.67/4.30  
% 10.67/4.30  Simplification rules
% 10.67/4.30  ----------------------
% 10.67/4.30  #Subsume      : 129
% 10.67/4.30  #Demod        : 6064
% 10.67/4.30  #Tautology    : 2222
% 10.67/4.30  #SimpNegUnit  : 8
% 10.67/4.30  #BackRed      : 27
% 10.67/4.30  
% 10.67/4.30  #Partial instantiations: 0
% 10.67/4.30  #Strategies tried      : 1
% 10.67/4.30  
% 10.67/4.30  Timing (in seconds)
% 10.67/4.30  ----------------------
% 10.67/4.30  Preprocessing        : 0.33
% 10.67/4.30  Parsing              : 0.18
% 10.67/4.30  CNF conversion       : 0.02
% 10.67/4.30  Main loop            : 3.16
% 10.67/4.30  Inferencing          : 0.60
% 10.67/4.30  Reduction            : 1.75
% 10.67/4.31  Demodulation         : 1.52
% 10.67/4.31  BG Simplification    : 0.09
% 10.67/4.31  Subsumption          : 0.55
% 10.67/4.31  Abstraction          : 0.10
% 10.67/4.31  MUC search           : 0.00
% 10.67/4.31  Cooper               : 0.00
% 10.67/4.31  Total                : 3.52
% 10.67/4.31  Index Insertion      : 0.00
% 10.67/4.31  Index Deletion       : 0.00
% 10.67/4.31  Index Matching       : 0.00
% 10.67/4.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
