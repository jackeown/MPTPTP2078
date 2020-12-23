%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:05 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 128 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  104 ( 203 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_28,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_95])).

tff(c_105,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_101])).

tff(c_85,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_442,plain,(
    ! [C_106,A_107,B_108] : k2_xboole_0(k2_zfmisc_1(C_106,A_107),k2_zfmisc_1(C_106,B_108)) = k2_zfmisc_1(C_106,k2_xboole_0(A_107,B_108)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k2_xboole_0(B_70,C_71))
      | ~ r1_tarski(k4_xboole_0(A_69,B_70),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_1825,plain,(
    ! [A_207,C_208,A_209,B_210] :
      ( r1_tarski(A_207,k2_zfmisc_1(C_208,k2_xboole_0(A_209,B_210)))
      | ~ r1_tarski(A_207,k2_zfmisc_1(C_208,B_210)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_207])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [C_66,B_67,A_68] :
      ( v5_relat_1(C_66,B_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_201,plain,(
    ! [A_17,B_67,A_68] :
      ( v5_relat_1(A_17,B_67)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_68,B_67)) ) ),
    inference(resolution,[status(thm)],[c_18,c_193])).

tff(c_1928,plain,(
    ! [A_211,A_212,B_213,C_214] :
      ( v5_relat_1(A_211,k2_xboole_0(A_212,B_213))
      | ~ r1_tarski(A_211,k2_zfmisc_1(C_214,B_213)) ) ),
    inference(resolution,[status(thm)],[c_1825,c_201])).

tff(c_1962,plain,(
    ! [A_212] : v5_relat_1('#skF_3',k2_xboole_0(A_212,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_1928])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_142,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_151,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_142])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( k7_relat_1(B_28,A_27) = B_28
      | ~ v4_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_151,c_30])).

tff(c_157,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_154])).

tff(c_32,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_30,A_29)),A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_161,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_32])).

tff(c_165,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_161])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_229,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(A_75,k2_xboole_0(C_76,B_77))
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_252,plain,(
    ! [A_75,A_1,B_2] :
      ( r1_tarski(A_75,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_75,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_229])).

tff(c_26,plain,(
    ! [A_24] :
      ( k2_xboole_0(k1_relat_1(A_24),k2_relat_1(A_24)) = k3_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_310,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(k2_xboole_0(A_85,C_86),B_87)
      | ~ r1_tarski(C_86,B_87)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1995,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(k3_relat_1(A_217),B_218)
      | ~ r1_tarski(k2_relat_1(A_217),B_218)
      | ~ r1_tarski(k1_relat_1(A_217),B_218)
      | ~ v1_relat_1(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_310])).

tff(c_38,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2054,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1995,c_38])).

tff(c_2078,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2054])).

tff(c_2094,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2078])).

tff(c_2106,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_252,c_2094])).

tff(c_2113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2106])).

tff(c_2114,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2078])).

tff(c_2245,plain,
    ( ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2114])).

tff(c_2251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1962,c_2245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.72  
% 3.85/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.72  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.85/1.72  
% 3.85/1.72  %Foreground sorts:
% 3.85/1.72  
% 3.85/1.72  
% 3.85/1.72  %Background operators:
% 3.85/1.72  
% 3.85/1.72  
% 3.85/1.72  %Foreground operators:
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.85/1.72  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.85/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.85/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.85/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.85/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.85/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.72  
% 3.85/1.74  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.85/1.74  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 3.85/1.74  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.85/1.74  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.74  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.85/1.74  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.85/1.74  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.85/1.74  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.85/1.74  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.85/1.74  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.85/1.74  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.85/1.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.85/1.74  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.85/1.74  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.85/1.74  tff(c_28, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.85/1.74  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.85/1.74  tff(c_95, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.74  tff(c_101, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_95])).
% 3.85/1.74  tff(c_105, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_101])).
% 3.85/1.74  tff(c_85, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.74  tff(c_93, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_85])).
% 3.85/1.74  tff(c_442, plain, (![C_106, A_107, B_108]: (k2_xboole_0(k2_zfmisc_1(C_106, A_107), k2_zfmisc_1(C_106, B_108))=k2_zfmisc_1(C_106, k2_xboole_0(A_107, B_108)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.85/1.74  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.74  tff(c_203, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k2_xboole_0(B_70, C_71)) | ~r1_tarski(k4_xboole_0(A_69, B_70), C_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.74  tff(c_207, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_4, c_203])).
% 3.85/1.74  tff(c_1825, plain, (![A_207, C_208, A_209, B_210]: (r1_tarski(A_207, k2_zfmisc_1(C_208, k2_xboole_0(A_209, B_210))) | ~r1_tarski(A_207, k2_zfmisc_1(C_208, B_210)))), inference(superposition, [status(thm), theory('equality')], [c_442, c_207])).
% 3.85/1.74  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.74  tff(c_193, plain, (![C_66, B_67, A_68]: (v5_relat_1(C_66, B_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.74  tff(c_201, plain, (![A_17, B_67, A_68]: (v5_relat_1(A_17, B_67) | ~r1_tarski(A_17, k2_zfmisc_1(A_68, B_67)))), inference(resolution, [status(thm)], [c_18, c_193])).
% 3.85/1.74  tff(c_1928, plain, (![A_211, A_212, B_213, C_214]: (v5_relat_1(A_211, k2_xboole_0(A_212, B_213)) | ~r1_tarski(A_211, k2_zfmisc_1(C_214, B_213)))), inference(resolution, [status(thm)], [c_1825, c_201])).
% 3.85/1.74  tff(c_1962, plain, (![A_212]: (v5_relat_1('#skF_3', k2_xboole_0(A_212, '#skF_2')))), inference(resolution, [status(thm)], [c_93, c_1928])).
% 3.85/1.74  tff(c_24, plain, (![B_23, A_22]: (r1_tarski(k2_relat_1(B_23), A_22) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.85/1.74  tff(c_142, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.74  tff(c_151, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_142])).
% 3.85/1.74  tff(c_30, plain, (![B_28, A_27]: (k7_relat_1(B_28, A_27)=B_28 | ~v4_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.85/1.74  tff(c_154, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_151, c_30])).
% 3.85/1.74  tff(c_157, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_154])).
% 3.85/1.74  tff(c_32, plain, (![B_30, A_29]: (r1_tarski(k1_relat_1(k7_relat_1(B_30, A_29)), A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.85/1.74  tff(c_161, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_157, c_32])).
% 3.85/1.74  tff(c_165, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_161])).
% 3.85/1.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.74  tff(c_229, plain, (![A_75, C_76, B_77]: (r1_tarski(A_75, k2_xboole_0(C_76, B_77)) | ~r1_tarski(A_75, B_77))), inference(resolution, [status(thm)], [c_4, c_203])).
% 3.85/1.74  tff(c_252, plain, (![A_75, A_1, B_2]: (r1_tarski(A_75, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_75, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_229])).
% 3.85/1.74  tff(c_26, plain, (![A_24]: (k2_xboole_0(k1_relat_1(A_24), k2_relat_1(A_24))=k3_relat_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.74  tff(c_310, plain, (![A_85, C_86, B_87]: (r1_tarski(k2_xboole_0(A_85, C_86), B_87) | ~r1_tarski(C_86, B_87) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/1.74  tff(c_1995, plain, (![A_217, B_218]: (r1_tarski(k3_relat_1(A_217), B_218) | ~r1_tarski(k2_relat_1(A_217), B_218) | ~r1_tarski(k1_relat_1(A_217), B_218) | ~v1_relat_1(A_217))), inference(superposition, [status(thm), theory('equality')], [c_26, c_310])).
% 3.85/1.74  tff(c_38, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.85/1.74  tff(c_2054, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1995, c_38])).
% 3.85/1.74  tff(c_2078, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2054])).
% 3.85/1.74  tff(c_2094, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2078])).
% 3.85/1.74  tff(c_2106, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_252, c_2094])).
% 3.85/1.74  tff(c_2113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_2106])).
% 3.85/1.74  tff(c_2114, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2078])).
% 3.85/1.74  tff(c_2245, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2114])).
% 3.85/1.74  tff(c_2251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_1962, c_2245])).
% 3.85/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.74  
% 3.85/1.74  Inference rules
% 4.15/1.74  ----------------------
% 4.15/1.74  #Ref     : 0
% 4.15/1.74  #Sup     : 595
% 4.15/1.74  #Fact    : 0
% 4.15/1.74  #Define  : 0
% 4.15/1.74  #Split   : 4
% 4.15/1.74  #Chain   : 0
% 4.15/1.74  #Close   : 0
% 4.15/1.74  
% 4.15/1.74  Ordering : KBO
% 4.15/1.74  
% 4.15/1.74  Simplification rules
% 4.15/1.74  ----------------------
% 4.15/1.74  #Subsume      : 148
% 4.15/1.74  #Demod        : 92
% 4.15/1.74  #Tautology    : 95
% 4.15/1.74  #SimpNegUnit  : 0
% 4.15/1.74  #BackRed      : 0
% 4.15/1.74  
% 4.15/1.74  #Partial instantiations: 0
% 4.15/1.74  #Strategies tried      : 1
% 4.15/1.74  
% 4.15/1.74  Timing (in seconds)
% 4.15/1.74  ----------------------
% 4.15/1.74  Preprocessing        : 0.29
% 4.15/1.74  Parsing              : 0.15
% 4.15/1.74  CNF conversion       : 0.02
% 4.15/1.74  Main loop            : 0.64
% 4.15/1.74  Inferencing          : 0.22
% 4.15/1.74  Reduction            : 0.23
% 4.15/1.74  Demodulation         : 0.18
% 4.15/1.74  BG Simplification    : 0.03
% 4.15/1.74  Subsumption          : 0.12
% 4.15/1.74  Abstraction          : 0.03
% 4.15/1.74  MUC search           : 0.00
% 4.15/1.74  Cooper               : 0.00
% 4.15/1.74  Total                : 0.96
% 4.15/1.74  Index Insertion      : 0.00
% 4.15/1.74  Index Deletion       : 0.00
% 4.15/1.74  Index Matching       : 0.00
% 4.15/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
