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
% DateTime   : Thu Dec  3 09:58:30 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.17s
% Verified   : 
% Statistics : Number of formulae       :   68 (  96 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 178 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    ! [A_29,B_31] :
      ( r1_tarski(k1_relat_1(A_29),k1_relat_1(B_31))
      | ~ r1_tarski(A_29,B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_390,plain,(
    ! [A_76] :
      ( k2_xboole_0(k1_relat_1(A_76),k2_relat_1(A_76)) = k3_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_474,plain,(
    ! [A_80] :
      ( r1_tarski(k1_relat_1(A_80),k3_relat_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_20])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28786,plain,(
    ! [A_446,A_447] :
      ( r1_tarski(A_446,k3_relat_1(A_447))
      | ~ r1_tarski(A_446,k1_relat_1(A_447))
      | ~ v1_relat_1(A_447) ) ),
    inference(resolution,[status(thm)],[c_474,c_12])).

tff(c_30,plain,(
    ! [A_28] :
      ( k2_xboole_0(k1_relat_1(A_28),k2_relat_1(A_28)) = k3_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_2301,plain,(
    ! [A_161,B_162] :
      ( k2_xboole_0(k2_relat_1(A_161),k2_relat_1(B_162)) = k2_relat_1(k2_xboole_0(A_161,B_162))
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4968,plain,(
    ! [A_210,B_211] :
      ( r1_tarski(k2_relat_1(A_210),k2_relat_1(k2_xboole_0(A_210,B_211)))
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2301,c_20])).

tff(c_5043,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_4968])).

tff(c_5073,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5043])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_tarski(k2_xboole_0(A_20,C_22),B_21)
      | ~ r1_tarski(C_22,B_21)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_208,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2771,plain,(
    ! [A_172,B_173] :
      ( k2_xboole_0(A_172,B_173) = A_172
      | ~ r1_tarski(k2_xboole_0(A_172,B_173),A_172) ) ),
    inference(resolution,[status(thm)],[c_20,c_208])).

tff(c_2784,plain,(
    ! [B_21,C_22] :
      ( k2_xboole_0(B_21,C_22) = B_21
      | ~ r1_tarski(C_22,B_21)
      | ~ r1_tarski(B_21,B_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_2771])).

tff(c_2834,plain,(
    ! [B_21,C_22] :
      ( k2_xboole_0(B_21,C_22) = B_21
      | ~ r1_tarski(C_22,B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2784])).

tff(c_5089,plain,(
    k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1('#skF_1')) = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5073,c_2834])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_530,plain,(
    ! [A_85,A_86,B_87] :
      ( r1_tarski(A_85,A_86)
      | ~ r1_tarski(A_85,k4_xboole_0(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_14,c_253])).

tff(c_544,plain,(
    ! [A_86,B_87,B_11] : r1_tarski(k4_xboole_0(k4_xboole_0(A_86,B_87),B_11),A_86) ),
    inference(resolution,[status(thm)],[c_14,c_530])).

tff(c_870,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(A_105,k2_xboole_0(B_106,C_107))
      | ~ r1_tarski(k4_xboole_0(A_105,B_106),C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_909,plain,(
    ! [A_86,B_87,B_11] : r1_tarski(k4_xboole_0(A_86,B_87),k2_xboole_0(B_11,A_86)) ),
    inference(resolution,[status(thm)],[c_544,c_870])).

tff(c_9764,plain,(
    ! [B_255] : r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'),B_255),k2_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5089,c_909])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k2_xboole_0(B_16,C_17))
      | ~ r1_tarski(k4_xboole_0(A_15,B_16),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9991,plain,(
    ! [B_260] : r1_tarski(k2_relat_1('#skF_1'),k2_xboole_0(B_260,k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_9764,c_18])).

tff(c_10053,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9991])).

tff(c_10090,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10053])).

tff(c_1338,plain,(
    ! [A_125,C_126,B_127] :
      ( r1_tarski(k2_xboole_0(A_125,C_126),B_127)
      | ~ r1_tarski(C_126,B_127)
      | ~ r1_tarski(A_125,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11442,plain,(
    ! [A_280,B_281] :
      ( r1_tarski(k3_relat_1(A_280),B_281)
      | ~ r1_tarski(k2_relat_1(A_280),B_281)
      | ~ r1_tarski(k1_relat_1(A_280),B_281)
      | ~ v1_relat_1(A_280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1338])).

tff(c_38,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11504,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_11442,c_38])).

tff(c_11528,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10090,c_11504])).

tff(c_28801,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28786,c_11528])).

tff(c_28836,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28801])).

tff(c_28857,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_28836])).

tff(c_28861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_28857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:16:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.17/4.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.17/4.40  
% 10.17/4.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.17/4.40  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.17/4.40  
% 10.17/4.40  %Foreground sorts:
% 10.17/4.40  
% 10.17/4.40  
% 10.17/4.40  %Background operators:
% 10.17/4.40  
% 10.17/4.40  
% 10.17/4.40  %Foreground operators:
% 10.17/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.17/4.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.17/4.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 10.17/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.17/4.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.17/4.40  tff('#skF_2', type, '#skF_2': $i).
% 10.17/4.40  tff('#skF_1', type, '#skF_1': $i).
% 10.17/4.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.17/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.17/4.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.17/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.17/4.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.17/4.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.17/4.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.17/4.40  
% 10.17/4.41  tff(f_104, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 10.17/4.41  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 10.17/4.41  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 10.17/4.41  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.17/4.41  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.17/4.41  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.17/4.41  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 10.17/4.41  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.17/4.41  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 10.17/4.41  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.17/4.41  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.17/4.41  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.17/4.41  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.17/4.41  tff(c_40, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.17/4.41  tff(c_34, plain, (![A_29, B_31]: (r1_tarski(k1_relat_1(A_29), k1_relat_1(B_31)) | ~r1_tarski(A_29, B_31) | ~v1_relat_1(B_31) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.17/4.41  tff(c_390, plain, (![A_76]: (k2_xboole_0(k1_relat_1(A_76), k2_relat_1(A_76))=k3_relat_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.17/4.41  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.17/4.41  tff(c_474, plain, (![A_80]: (r1_tarski(k1_relat_1(A_80), k3_relat_1(A_80)) | ~v1_relat_1(A_80))), inference(superposition, [status(thm), theory('equality')], [c_390, c_20])).
% 10.17/4.41  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.17/4.41  tff(c_28786, plain, (![A_446, A_447]: (r1_tarski(A_446, k3_relat_1(A_447)) | ~r1_tarski(A_446, k1_relat_1(A_447)) | ~v1_relat_1(A_447))), inference(resolution, [status(thm)], [c_474, c_12])).
% 10.17/4.41  tff(c_30, plain, (![A_28]: (k2_xboole_0(k1_relat_1(A_28), k2_relat_1(A_28))=k3_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.17/4.41  tff(c_104, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.17/4.41  tff(c_123, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_104])).
% 10.17/4.41  tff(c_2301, plain, (![A_161, B_162]: (k2_xboole_0(k2_relat_1(A_161), k2_relat_1(B_162))=k2_relat_1(k2_xboole_0(A_161, B_162)) | ~v1_relat_1(B_162) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.17/4.41  tff(c_4968, plain, (![A_210, B_211]: (r1_tarski(k2_relat_1(A_210), k2_relat_1(k2_xboole_0(A_210, B_211))) | ~v1_relat_1(B_211) | ~v1_relat_1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_2301, c_20])).
% 10.17/4.41  tff(c_5043, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_123, c_4968])).
% 10.17/4.41  tff(c_5073, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_5043])).
% 10.17/4.41  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.17/4.41  tff(c_22, plain, (![A_20, C_22, B_21]: (r1_tarski(k2_xboole_0(A_20, C_22), B_21) | ~r1_tarski(C_22, B_21) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.17/4.41  tff(c_208, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.17/4.41  tff(c_2771, plain, (![A_172, B_173]: (k2_xboole_0(A_172, B_173)=A_172 | ~r1_tarski(k2_xboole_0(A_172, B_173), A_172))), inference(resolution, [status(thm)], [c_20, c_208])).
% 10.17/4.41  tff(c_2784, plain, (![B_21, C_22]: (k2_xboole_0(B_21, C_22)=B_21 | ~r1_tarski(C_22, B_21) | ~r1_tarski(B_21, B_21))), inference(resolution, [status(thm)], [c_22, c_2771])).
% 10.17/4.41  tff(c_2834, plain, (![B_21, C_22]: (k2_xboole_0(B_21, C_22)=B_21 | ~r1_tarski(C_22, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2784])).
% 10.17/4.41  tff(c_5089, plain, (k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1('#skF_1'))=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5073, c_2834])).
% 10.17/4.41  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.17/4.41  tff(c_253, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.17/4.41  tff(c_530, plain, (![A_85, A_86, B_87]: (r1_tarski(A_85, A_86) | ~r1_tarski(A_85, k4_xboole_0(A_86, B_87)))), inference(resolution, [status(thm)], [c_14, c_253])).
% 10.17/4.41  tff(c_544, plain, (![A_86, B_87, B_11]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_86, B_87), B_11), A_86))), inference(resolution, [status(thm)], [c_14, c_530])).
% 10.17/4.41  tff(c_870, plain, (![A_105, B_106, C_107]: (r1_tarski(A_105, k2_xboole_0(B_106, C_107)) | ~r1_tarski(k4_xboole_0(A_105, B_106), C_107))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.17/4.41  tff(c_909, plain, (![A_86, B_87, B_11]: (r1_tarski(k4_xboole_0(A_86, B_87), k2_xboole_0(B_11, A_86)))), inference(resolution, [status(thm)], [c_544, c_870])).
% 10.17/4.41  tff(c_9764, plain, (![B_255]: (r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'), B_255), k2_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5089, c_909])).
% 10.17/4.41  tff(c_18, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k2_xboole_0(B_16, C_17)) | ~r1_tarski(k4_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.17/4.41  tff(c_9991, plain, (![B_260]: (r1_tarski(k2_relat_1('#skF_1'), k2_xboole_0(B_260, k2_relat_1('#skF_2'))))), inference(resolution, [status(thm)], [c_9764, c_18])).
% 10.17/4.41  tff(c_10053, plain, (r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_9991])).
% 10.17/4.41  tff(c_10090, plain, (r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10053])).
% 10.17/4.41  tff(c_1338, plain, (![A_125, C_126, B_127]: (r1_tarski(k2_xboole_0(A_125, C_126), B_127) | ~r1_tarski(C_126, B_127) | ~r1_tarski(A_125, B_127))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.17/4.41  tff(c_11442, plain, (![A_280, B_281]: (r1_tarski(k3_relat_1(A_280), B_281) | ~r1_tarski(k2_relat_1(A_280), B_281) | ~r1_tarski(k1_relat_1(A_280), B_281) | ~v1_relat_1(A_280))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1338])).
% 10.17/4.41  tff(c_38, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.17/4.41  tff(c_11504, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_11442, c_38])).
% 10.17/4.41  tff(c_11528, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10090, c_11504])).
% 10.17/4.41  tff(c_28801, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28786, c_11528])).
% 10.17/4.41  tff(c_28836, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28801])).
% 10.17/4.41  tff(c_28857, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_28836])).
% 10.17/4.41  tff(c_28861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_28857])).
% 10.17/4.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.17/4.41  
% 10.17/4.41  Inference rules
% 10.17/4.41  ----------------------
% 10.17/4.41  #Ref     : 0
% 10.17/4.41  #Sup     : 7044
% 10.17/4.41  #Fact    : 0
% 10.17/4.41  #Define  : 0
% 10.17/4.41  #Split   : 5
% 10.17/4.41  #Chain   : 0
% 10.17/4.41  #Close   : 0
% 10.17/4.41  
% 10.17/4.41  Ordering : KBO
% 10.17/4.41  
% 10.17/4.41  Simplification rules
% 10.17/4.41  ----------------------
% 10.17/4.41  #Subsume      : 1166
% 10.17/4.41  #Demod        : 5557
% 10.17/4.41  #Tautology    : 3933
% 10.17/4.41  #SimpNegUnit  : 7
% 10.17/4.41  #BackRed      : 5
% 10.17/4.41  
% 10.17/4.41  #Partial instantiations: 0
% 10.17/4.41  #Strategies tried      : 1
% 10.17/4.41  
% 10.17/4.41  Timing (in seconds)
% 10.17/4.41  ----------------------
% 10.17/4.42  Preprocessing        : 0.31
% 10.17/4.42  Parsing              : 0.17
% 10.17/4.42  CNF conversion       : 0.02
% 10.17/4.42  Main loop            : 3.34
% 10.17/4.42  Inferencing          : 0.63
% 10.17/4.42  Reduction            : 1.72
% 10.17/4.42  Demodulation         : 1.48
% 10.17/4.42  BG Simplification    : 0.07
% 10.17/4.42  Subsumption          : 0.76
% 10.17/4.42  Abstraction          : 0.11
% 10.17/4.42  MUC search           : 0.00
% 10.17/4.42  Cooper               : 0.00
% 10.17/4.42  Total                : 3.68
% 10.17/4.42  Index Insertion      : 0.00
% 10.17/4.42  Index Deletion       : 0.00
% 10.17/4.42  Index Matching       : 0.00
% 10.17/4.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
