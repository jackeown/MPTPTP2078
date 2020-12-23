%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:13 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 416 expanded)
%              Number of leaves         :   35 ( 151 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 736 expanded)
%              Number of equality atoms :   47 ( 246 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_87,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_80,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_93,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_66,plain,(
    ! [A_36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_180,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(B_56,A_57)
      | ~ m1_subset_1(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_184,plain,(
    ! [B_56,A_21] :
      ( r1_tarski(B_56,A_21)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_180,c_34])).

tff(c_203,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_184])).

tff(c_216,plain,(
    ! [A_36] : r1_tarski(k1_xboole_0,A_36) ),
    inference(resolution,[status(thm)],[c_66,c_203])).

tff(c_54,plain,(
    ! [A_28] : k1_subset_1(A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_29] : k2_subset_1(A_29) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    ! [A_35] : k3_subset_1(A_35,k1_subset_1(A_35)) = k2_subset_1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    ! [A_35] : k3_subset_1(A_35,k1_subset_1(A_35)) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_64])).

tff(c_80,plain,(
    ! [A_35] : k3_subset_1(A_35,k1_xboole_0) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_78])).

tff(c_607,plain,(
    ! [A_104,B_105] :
      ( k3_subset_1(A_104,k3_subset_1(A_104,B_105)) = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_616,plain,(
    ! [A_36] : k3_subset_1(A_36,k3_subset_1(A_36,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_607])).

tff(c_621,plain,(
    ! [A_36] : k3_subset_1(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_616])).

tff(c_70,plain,
    ( k2_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,
    ( '#skF_7' != '#skF_6'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_70])).

tff(c_155,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_76,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | k2_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_79,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76])).

tff(c_162,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_79])).

tff(c_163,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_155])).

tff(c_622,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_163])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_622])).

tff(c_626,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_1286,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(A_166,B_167) = k3_subset_1(A_166,B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1299,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_xboole_0) = k3_subset_1(A_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_66,c_1286])).

tff(c_1304,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_xboole_0) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1299])).

tff(c_1222,plain,(
    ! [A_162,B_163] :
      ( k3_subset_1(A_162,k3_subset_1(A_162,B_163)) = B_163
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1231,plain,(
    ! [A_36] : k3_subset_1(A_36,k3_subset_1(A_36,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_1222])).

tff(c_1236,plain,(
    ! [A_36] : k3_subset_1(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1231])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_793,plain,(
    ! [A_128,B_129] :
      ( ~ r2_hidden('#skF_1'(A_128,B_129),B_129)
      | r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_807,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_793])).

tff(c_36,plain,(
    ! [C_25,A_21] :
      ( r2_hidden(C_25,k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_655,plain,(
    ! [B_116,A_117] :
      ( m1_subset_1(B_116,A_117)
      | ~ r2_hidden(B_116,A_117)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_664,plain,(
    ! [C_25,A_21] :
      ( m1_subset_1(C_25,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(resolution,[status(thm)],[c_36,c_655])).

tff(c_669,plain,(
    ! [C_25,A_21] :
      ( m1_subset_1(C_25,k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_664])).

tff(c_1722,plain,(
    ! [A_196,C_197] :
      ( k4_xboole_0(A_196,C_197) = k3_subset_1(A_196,C_197)
      | ~ r1_tarski(C_197,A_196) ) ),
    inference(resolution,[status(thm)],[c_669,c_1286])).

tff(c_1731,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_subset_1(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_807,c_1722])).

tff(c_1745,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_1731])).

tff(c_4047,plain,(
    ! [A_298,B_299,C_300] :
      ( r2_hidden('#skF_2'(A_298,B_299,C_300),A_298)
      | r2_hidden('#skF_3'(A_298,B_299,C_300),C_300)
      | k4_xboole_0(A_298,B_299) = C_300 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4050,plain,(
    ! [A_298,C_300] :
      ( r2_hidden('#skF_3'(A_298,A_298,C_300),C_300)
      | k4_xboole_0(A_298,A_298) = C_300 ) ),
    inference(resolution,[status(thm)],[c_4047,c_24])).

tff(c_4170,plain,(
    ! [A_302,C_303] :
      ( r2_hidden('#skF_3'(A_302,A_302,C_303),C_303)
      | k1_xboole_0 = C_303 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_4050])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1302,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1286])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1390,plain,(
    ! [D_13] :
      ( r2_hidden(D_13,'#skF_6')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_14])).

tff(c_4211,plain,(
    ! [A_302] :
      ( r2_hidden('#skF_3'(A_302,A_302,k3_subset_1('#skF_6','#skF_7')),'#skF_6')
      | k3_subset_1('#skF_6','#skF_7') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4170,c_1390])).

tff(c_5010,plain,(
    k3_subset_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4211])).

tff(c_1234,plain,(
    k3_subset_1('#skF_6',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_68,c_1222])).

tff(c_627,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_647,plain,(
    ! [B_114,A_115] :
      ( r2_hidden(B_114,A_115)
      | ~ m1_subset_1(B_114,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_651,plain,(
    ! [B_114,A_21] :
      ( r1_tarski(B_114,A_21)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_647,c_34])).

tff(c_670,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_119)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_651])).

tff(c_682,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_670])).

tff(c_993,plain,(
    ! [A_141,C_142,B_143] :
      ( r1_tarski(A_141,C_142)
      | ~ r1_tarski(B_143,C_142)
      | ~ r1_tarski(A_141,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1017,plain,(
    ! [A_146] :
      ( r1_tarski(A_146,'#skF_6')
      | ~ r1_tarski(A_146,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_682,c_993])).

tff(c_1033,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_627,c_1017])).

tff(c_1728,plain,(
    k4_xboole_0('#skF_6',k3_subset_1('#skF_6','#skF_7')) = k3_subset_1('#skF_6',k3_subset_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1033,c_1722])).

tff(c_1743,plain,(
    k4_xboole_0('#skF_6',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1728])).

tff(c_5020,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5010,c_1743])).

tff(c_5040,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_5020])).

tff(c_5042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_5040])).

tff(c_5043,plain,(
    ! [A_302] : r2_hidden('#skF_3'(A_302,A_302,k3_subset_1('#skF_6','#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4211])).

tff(c_1408,plain,(
    ! [D_173,A_174,B_175] :
      ( r2_hidden(D_173,k4_xboole_0(A_174,B_175))
      | r2_hidden(D_173,B_175)
      | ~ r2_hidden(D_173,A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1634,plain,(
    ! [D_190] :
      ( r2_hidden(D_190,k3_subset_1('#skF_6','#skF_7'))
      | r2_hidden(D_190,'#skF_7')
      | ~ r2_hidden(D_190,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_1408])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5265,plain,(
    ! [D_352,B_353] :
      ( r2_hidden(D_352,B_353)
      | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_353)
      | r2_hidden(D_352,'#skF_7')
      | ~ r2_hidden(D_352,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1634,c_4])).

tff(c_5276,plain,(
    ! [D_354] :
      ( r2_hidden(D_354,'#skF_7')
      | ~ r2_hidden(D_354,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_627,c_5265])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1387,plain,(
    ! [D_13] :
      ( ~ r2_hidden(D_13,'#skF_7')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_12])).

tff(c_4213,plain,(
    ! [A_302] :
      ( ~ r2_hidden('#skF_3'(A_302,A_302,k3_subset_1('#skF_6','#skF_7')),'#skF_7')
      | k3_subset_1('#skF_6','#skF_7') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4170,c_1387])).

tff(c_4756,plain,(
    ! [A_302] : ~ r2_hidden('#skF_3'(A_302,A_302,k3_subset_1('#skF_6','#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4213])).

tff(c_5279,plain,(
    ! [A_302] : ~ r2_hidden('#skF_3'(A_302,A_302,k3_subset_1('#skF_6','#skF_7')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5276,c_4756])).

tff(c_5314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5043,c_5279])).

tff(c_5315,plain,(
    k3_subset_1('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4213])).

tff(c_5324,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_1743])).

tff(c_5344,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_5324])).

tff(c_5346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_5344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.21  
% 5.73/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.21  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 5.73/2.21  
% 5.73/2.21  %Foreground sorts:
% 5.73/2.21  
% 5.73/2.21  
% 5.73/2.21  %Background operators:
% 5.73/2.21  
% 5.73/2.21  
% 5.73/2.21  %Foreground operators:
% 5.73/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.73/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.21  tff('#skF_7', type, '#skF_7': $i).
% 5.73/2.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.73/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.73/2.21  tff('#skF_6', type, '#skF_6': $i).
% 5.73/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.73/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.73/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.73/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.21  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.73/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.73/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.73/2.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.73/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.73/2.21  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.73/2.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.73/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.73/2.21  
% 5.73/2.23  tff(f_95, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.73/2.23  tff(f_87, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.73/2.23  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.73/2.23  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.73/2.23  tff(f_78, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.73/2.23  tff(f_80, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.73/2.23  tff(f_93, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 5.73/2.23  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.73/2.23  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 5.73/2.23  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.73/2.23  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.73/2.23  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.73/2.23  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.73/2.23  tff(c_66, plain, (![A_36]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.73/2.23  tff(c_60, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.73/2.23  tff(c_180, plain, (![B_56, A_57]: (r2_hidden(B_56, A_57) | ~m1_subset_1(B_56, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.73/2.23  tff(c_34, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.73/2.23  tff(c_184, plain, (![B_56, A_21]: (r1_tarski(B_56, A_21) | ~m1_subset_1(B_56, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_180, c_34])).
% 5.73/2.23  tff(c_203, plain, (![B_60, A_61]: (r1_tarski(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)))), inference(negUnitSimplification, [status(thm)], [c_60, c_184])).
% 5.73/2.23  tff(c_216, plain, (![A_36]: (r1_tarski(k1_xboole_0, A_36))), inference(resolution, [status(thm)], [c_66, c_203])).
% 5.73/2.23  tff(c_54, plain, (![A_28]: (k1_subset_1(A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.23  tff(c_56, plain, (![A_29]: (k2_subset_1(A_29)=A_29)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.73/2.23  tff(c_64, plain, (![A_35]: (k3_subset_1(A_35, k1_subset_1(A_35))=k2_subset_1(A_35))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.73/2.23  tff(c_78, plain, (![A_35]: (k3_subset_1(A_35, k1_subset_1(A_35))=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_64])).
% 5.73/2.23  tff(c_80, plain, (![A_35]: (k3_subset_1(A_35, k1_xboole_0)=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_78])).
% 5.73/2.23  tff(c_607, plain, (![A_104, B_105]: (k3_subset_1(A_104, k3_subset_1(A_104, B_105))=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.23  tff(c_616, plain, (![A_36]: (k3_subset_1(A_36, k3_subset_1(A_36, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_607])).
% 5.73/2.23  tff(c_621, plain, (![A_36]: (k3_subset_1(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_616])).
% 5.73/2.23  tff(c_70, plain, (k2_subset_1('#skF_6')!='#skF_7' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.73/2.23  tff(c_77, plain, ('#skF_7'!='#skF_6' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_70])).
% 5.73/2.23  tff(c_155, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_77])).
% 5.73/2.23  tff(c_76, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | k2_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.73/2.23  tff(c_79, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76])).
% 5.73/2.23  tff(c_162, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_155, c_79])).
% 5.73/2.23  tff(c_163, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_155])).
% 5.73/2.23  tff(c_622, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_163])).
% 5.73/2.23  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_622])).
% 5.73/2.23  tff(c_626, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_77])).
% 5.73/2.23  tff(c_1286, plain, (![A_166, B_167]: (k4_xboole_0(A_166, B_167)=k3_subset_1(A_166, B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.73/2.23  tff(c_1299, plain, (![A_36]: (k4_xboole_0(A_36, k1_xboole_0)=k3_subset_1(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_66, c_1286])).
% 5.73/2.23  tff(c_1304, plain, (![A_36]: (k4_xboole_0(A_36, k1_xboole_0)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1299])).
% 5.73/2.23  tff(c_1222, plain, (![A_162, B_163]: (k3_subset_1(A_162, k3_subset_1(A_162, B_163))=B_163 | ~m1_subset_1(B_163, k1_zfmisc_1(A_162)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.23  tff(c_1231, plain, (![A_36]: (k3_subset_1(A_36, k3_subset_1(A_36, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_1222])).
% 5.73/2.23  tff(c_1236, plain, (![A_36]: (k3_subset_1(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1231])).
% 5.73/2.23  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.73/2.23  tff(c_793, plain, (![A_128, B_129]: (~r2_hidden('#skF_1'(A_128, B_129), B_129) | r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.73/2.23  tff(c_807, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_793])).
% 5.73/2.23  tff(c_36, plain, (![C_25, A_21]: (r2_hidden(C_25, k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.73/2.23  tff(c_655, plain, (![B_116, A_117]: (m1_subset_1(B_116, A_117) | ~r2_hidden(B_116, A_117) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.73/2.23  tff(c_664, plain, (![C_25, A_21]: (m1_subset_1(C_25, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(resolution, [status(thm)], [c_36, c_655])).
% 5.73/2.23  tff(c_669, plain, (![C_25, A_21]: (m1_subset_1(C_25, k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(negUnitSimplification, [status(thm)], [c_60, c_664])).
% 5.73/2.23  tff(c_1722, plain, (![A_196, C_197]: (k4_xboole_0(A_196, C_197)=k3_subset_1(A_196, C_197) | ~r1_tarski(C_197, A_196))), inference(resolution, [status(thm)], [c_669, c_1286])).
% 5.73/2.23  tff(c_1731, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_subset_1(A_3, A_3))), inference(resolution, [status(thm)], [c_807, c_1722])).
% 5.73/2.23  tff(c_1745, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1236, c_1731])).
% 5.73/2.23  tff(c_4047, plain, (![A_298, B_299, C_300]: (r2_hidden('#skF_2'(A_298, B_299, C_300), A_298) | r2_hidden('#skF_3'(A_298, B_299, C_300), C_300) | k4_xboole_0(A_298, B_299)=C_300)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.73/2.23  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.73/2.23  tff(c_4050, plain, (![A_298, C_300]: (r2_hidden('#skF_3'(A_298, A_298, C_300), C_300) | k4_xboole_0(A_298, A_298)=C_300)), inference(resolution, [status(thm)], [c_4047, c_24])).
% 5.73/2.23  tff(c_4170, plain, (![A_302, C_303]: (r2_hidden('#skF_3'(A_302, A_302, C_303), C_303) | k1_xboole_0=C_303)), inference(demodulation, [status(thm), theory('equality')], [c_1745, c_4050])).
% 5.73/2.23  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.73/2.23  tff(c_1302, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_1286])).
% 5.73/2.23  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.73/2.23  tff(c_1390, plain, (![D_13]: (r2_hidden(D_13, '#skF_6') | ~r2_hidden(D_13, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_14])).
% 5.73/2.23  tff(c_4211, plain, (![A_302]: (r2_hidden('#skF_3'(A_302, A_302, k3_subset_1('#skF_6', '#skF_7')), '#skF_6') | k3_subset_1('#skF_6', '#skF_7')=k1_xboole_0)), inference(resolution, [status(thm)], [c_4170, c_1390])).
% 5.73/2.23  tff(c_5010, plain, (k3_subset_1('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4211])).
% 5.73/2.23  tff(c_1234, plain, (k3_subset_1('#skF_6', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_68, c_1222])).
% 5.73/2.23  tff(c_627, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_77])).
% 5.73/2.23  tff(c_647, plain, (![B_114, A_115]: (r2_hidden(B_114, A_115) | ~m1_subset_1(B_114, A_115) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.73/2.23  tff(c_651, plain, (![B_114, A_21]: (r1_tarski(B_114, A_21) | ~m1_subset_1(B_114, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_647, c_34])).
% 5.73/2.23  tff(c_670, plain, (![B_118, A_119]: (r1_tarski(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(A_119)))), inference(negUnitSimplification, [status(thm)], [c_60, c_651])).
% 5.73/2.23  tff(c_682, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_670])).
% 5.73/2.23  tff(c_993, plain, (![A_141, C_142, B_143]: (r1_tarski(A_141, C_142) | ~r1_tarski(B_143, C_142) | ~r1_tarski(A_141, B_143))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.73/2.23  tff(c_1017, plain, (![A_146]: (r1_tarski(A_146, '#skF_6') | ~r1_tarski(A_146, '#skF_7'))), inference(resolution, [status(thm)], [c_682, c_993])).
% 5.73/2.23  tff(c_1033, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_627, c_1017])).
% 5.73/2.23  tff(c_1728, plain, (k4_xboole_0('#skF_6', k3_subset_1('#skF_6', '#skF_7'))=k3_subset_1('#skF_6', k3_subset_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1033, c_1722])).
% 5.73/2.23  tff(c_1743, plain, (k4_xboole_0('#skF_6', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1728])).
% 5.73/2.23  tff(c_5020, plain, (k4_xboole_0('#skF_6', k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5010, c_1743])).
% 5.73/2.23  tff(c_5040, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_5020])).
% 5.73/2.23  tff(c_5042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_626, c_5040])).
% 5.73/2.23  tff(c_5043, plain, (![A_302]: (r2_hidden('#skF_3'(A_302, A_302, k3_subset_1('#skF_6', '#skF_7')), '#skF_6'))), inference(splitRight, [status(thm)], [c_4211])).
% 5.73/2.23  tff(c_1408, plain, (![D_173, A_174, B_175]: (r2_hidden(D_173, k4_xboole_0(A_174, B_175)) | r2_hidden(D_173, B_175) | ~r2_hidden(D_173, A_174))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.73/2.23  tff(c_1634, plain, (![D_190]: (r2_hidden(D_190, k3_subset_1('#skF_6', '#skF_7')) | r2_hidden(D_190, '#skF_7') | ~r2_hidden(D_190, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_1408])).
% 5.73/2.23  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.73/2.23  tff(c_5265, plain, (![D_352, B_353]: (r2_hidden(D_352, B_353) | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_353) | r2_hidden(D_352, '#skF_7') | ~r2_hidden(D_352, '#skF_6'))), inference(resolution, [status(thm)], [c_1634, c_4])).
% 5.73/2.23  tff(c_5276, plain, (![D_354]: (r2_hidden(D_354, '#skF_7') | ~r2_hidden(D_354, '#skF_6'))), inference(resolution, [status(thm)], [c_627, c_5265])).
% 5.73/2.23  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.73/2.23  tff(c_1387, plain, (![D_13]: (~r2_hidden(D_13, '#skF_7') | ~r2_hidden(D_13, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_12])).
% 5.73/2.23  tff(c_4213, plain, (![A_302]: (~r2_hidden('#skF_3'(A_302, A_302, k3_subset_1('#skF_6', '#skF_7')), '#skF_7') | k3_subset_1('#skF_6', '#skF_7')=k1_xboole_0)), inference(resolution, [status(thm)], [c_4170, c_1387])).
% 5.73/2.23  tff(c_4756, plain, (![A_302]: (~r2_hidden('#skF_3'(A_302, A_302, k3_subset_1('#skF_6', '#skF_7')), '#skF_7'))), inference(splitLeft, [status(thm)], [c_4213])).
% 5.73/2.23  tff(c_5279, plain, (![A_302]: (~r2_hidden('#skF_3'(A_302, A_302, k3_subset_1('#skF_6', '#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_5276, c_4756])).
% 5.73/2.23  tff(c_5314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5043, c_5279])).
% 5.73/2.23  tff(c_5315, plain, (k3_subset_1('#skF_6', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4213])).
% 5.73/2.23  tff(c_5324, plain, (k4_xboole_0('#skF_6', k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5315, c_1743])).
% 5.73/2.23  tff(c_5344, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_5324])).
% 5.73/2.23  tff(c_5346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_626, c_5344])).
% 5.73/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.23  
% 5.73/2.23  Inference rules
% 5.73/2.23  ----------------------
% 5.73/2.23  #Ref     : 0
% 5.73/2.23  #Sup     : 1187
% 5.73/2.23  #Fact    : 0
% 5.73/2.23  #Define  : 0
% 5.73/2.23  #Split   : 18
% 5.73/2.23  #Chain   : 0
% 5.73/2.23  #Close   : 0
% 5.73/2.23  
% 5.73/2.23  Ordering : KBO
% 5.73/2.23  
% 5.73/2.23  Simplification rules
% 5.73/2.23  ----------------------
% 5.73/2.23  #Subsume      : 183
% 5.73/2.23  #Demod        : 493
% 5.73/2.23  #Tautology    : 472
% 5.73/2.23  #SimpNegUnit  : 50
% 5.73/2.23  #BackRed      : 146
% 5.73/2.23  
% 5.73/2.23  #Partial instantiations: 0
% 5.73/2.23  #Strategies tried      : 1
% 5.73/2.23  
% 5.73/2.23  Timing (in seconds)
% 5.73/2.23  ----------------------
% 5.73/2.23  Preprocessing        : 0.35
% 5.73/2.23  Parsing              : 0.18
% 5.73/2.23  CNF conversion       : 0.03
% 5.73/2.23  Main loop            : 1.03
% 5.73/2.23  Inferencing          : 0.35
% 5.73/2.23  Reduction            : 0.34
% 5.73/2.23  Demodulation         : 0.24
% 5.73/2.23  BG Simplification    : 0.04
% 5.73/2.23  Subsumption          : 0.21
% 5.73/2.23  Abstraction          : 0.05
% 5.73/2.23  MUC search           : 0.00
% 5.73/2.23  Cooper               : 0.00
% 5.73/2.23  Total                : 1.42
% 5.73/2.23  Index Insertion      : 0.00
% 5.73/2.23  Index Deletion       : 0.00
% 5.73/2.23  Index Matching       : 0.00
% 5.73/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
