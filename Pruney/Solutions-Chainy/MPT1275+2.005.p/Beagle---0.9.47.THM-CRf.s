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
% DateTime   : Thu Dec  3 10:22:02 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 167 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 376 expanded)
%              Number of equality atoms :   33 (  92 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_60,plain,
    ( k2_tops_1('#skF_4','#skF_5') != '#skF_5'
    | ~ v3_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_102,plain,(
    ~ v3_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,
    ( v3_tops_1('#skF_5','#skF_4')
    | k2_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_103,plain,(
    k2_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_66])).

tff(c_322,plain,(
    ! [B_89,A_90] :
      ( v2_tops_1(B_89,A_90)
      | ~ r1_tarski(B_89,k2_tops_1(A_90,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_324,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_322])).

tff(c_326,plain,(
    v2_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_32,c_324])).

tff(c_54,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_297,plain,(
    ! [A_83,B_84] :
      ( k2_pre_topc(A_83,B_84) = B_84
      | ~ v4_pre_topc(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_300,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_297])).

tff(c_303,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_300])).

tff(c_466,plain,(
    ! [B_116,A_117] :
      ( v3_tops_1(B_116,A_117)
      | ~ v2_tops_1(k2_pre_topc(A_117,B_116),A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_468,plain,
    ( v3_tops_1('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_466])).

tff(c_470,plain,(
    v3_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_326,c_468])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_470])).

tff(c_473,plain,(
    k2_tops_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_474,plain,(
    v3_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_632,plain,(
    ! [B_152,A_153] :
      ( v2_tops_1(B_152,A_153)
      | ~ v3_tops_1(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_635,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | ~ v3_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_632])).

tff(c_638,plain,(
    v2_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_474,c_635])).

tff(c_744,plain,(
    ! [B_174,A_175] :
      ( r1_tarski(B_174,k2_tops_1(A_175,B_174))
      | ~ v2_tops_1(B_174,A_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_746,plain,
    ( r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5'))
    | ~ v2_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_744])).

tff(c_749,plain,(
    r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_638,c_746])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_520,plain,(
    ! [A_133,B_134,C_135] :
      ( k9_subset_1(A_133,B_134,C_135) = k3_xboole_0(B_134,C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_523,plain,(
    ! [B_134] : k9_subset_1(u1_struct_0('#skF_4'),B_134,'#skF_5') = k3_xboole_0(B_134,'#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_520])).

tff(c_575,plain,(
    ! [A_143,C_144,B_145] :
      ( k9_subset_1(A_143,C_144,B_145) = k9_subset_1(A_143,B_145,C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_577,plain,(
    ! [B_145] : k9_subset_1(u1_struct_0('#skF_4'),B_145,'#skF_5') = k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_145) ),
    inference(resolution,[status(thm)],[c_56,c_575])).

tff(c_579,plain,(
    ! [B_145] : k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_145) = k3_xboole_0(B_145,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_577])).

tff(c_666,plain,(
    ! [A_160,B_161] :
      ( k2_pre_topc(A_160,B_161) = B_161
      | ~ v4_pre_topc(B_161,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_669,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_666])).

tff(c_672,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_669])).

tff(c_1806,plain,(
    ! [A_320,B_321] :
      ( k9_subset_1(u1_struct_0(A_320),k2_pre_topc(A_320,B_321),k2_pre_topc(A_320,k3_subset_1(u1_struct_0(A_320),B_321))) = k2_tops_1(A_320,B_321)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1815,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_1806])).

tff(c_1819,plain,(
    k3_xboole_0('#skF_5',k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5'))) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2,c_579,c_1815])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_490,plain,(
    ! [D_123,A_124,B_125] :
      ( r2_hidden(D_123,A_124)
      | ~ r2_hidden(D_123,k3_xboole_0(A_124,B_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_597,plain,(
    ! [A_147,B_148,B_149] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_147,B_148),B_149),A_147)
      | r1_tarski(k3_xboole_0(A_147,B_148),B_149) ) ),
    inference(resolution,[status(thm)],[c_8,c_490])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_622,plain,(
    ! [A_150,B_151] : r1_tarski(k3_xboole_0(A_150,B_151),A_150) ),
    inference(resolution,[status(thm)],[c_597,c_6])).

tff(c_639,plain,(
    ! [B_154,A_155] : r1_tarski(k3_xboole_0(B_154,A_155),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_622])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_659,plain,(
    ! [B_158,A_159] :
      ( k3_xboole_0(B_158,A_159) = A_159
      | ~ r1_tarski(A_159,k3_xboole_0(B_158,A_159)) ) ),
    inference(resolution,[status(thm)],[c_639,c_28])).

tff(c_665,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(B_2,A_1) = A_1
      | ~ r1_tarski(A_1,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_659])).

tff(c_1904,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k3_subset_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_665])).

tff(c_1958,plain,(
    k2_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_1819,c_2,c_1904])).

tff(c_1960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_1958])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:04:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.89  
% 4.45/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.89  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.45/1.89  
% 4.45/1.89  %Foreground sorts:
% 4.45/1.89  
% 4.45/1.89  
% 4.45/1.89  %Background operators:
% 4.45/1.89  
% 4.45/1.89  
% 4.45/1.89  %Foreground operators:
% 4.45/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.89  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.45/1.89  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.45/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.89  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.45/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.45/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.45/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.45/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.45/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.45/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.45/1.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.45/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.89  
% 4.45/1.90  tff(f_118, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 4.45/1.90  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.45/1.90  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 4.45/1.90  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.45/1.90  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 4.45/1.90  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 4.45/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.45/1.90  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.45/1.90  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.45/1.90  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 4.45/1.90  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.45/1.90  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.45/1.90  tff(c_60, plain, (k2_tops_1('#skF_4', '#skF_5')!='#skF_5' | ~v3_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.90  tff(c_102, plain, (~v3_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.45/1.90  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.90  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.90  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.45/1.90  tff(c_66, plain, (v3_tops_1('#skF_5', '#skF_4') | k2_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.90  tff(c_103, plain, (k2_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_102, c_66])).
% 4.45/1.90  tff(c_322, plain, (![B_89, A_90]: (v2_tops_1(B_89, A_90) | ~r1_tarski(B_89, k2_tops_1(A_90, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.45/1.90  tff(c_324, plain, (v2_tops_1('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_103, c_322])).
% 4.45/1.90  tff(c_326, plain, (v2_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_32, c_324])).
% 4.45/1.90  tff(c_54, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.45/1.90  tff(c_297, plain, (![A_83, B_84]: (k2_pre_topc(A_83, B_84)=B_84 | ~v4_pre_topc(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.45/1.90  tff(c_300, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_297])).
% 4.45/1.90  tff(c_303, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_300])).
% 4.45/1.90  tff(c_466, plain, (![B_116, A_117]: (v3_tops_1(B_116, A_117) | ~v2_tops_1(k2_pre_topc(A_117, B_116), A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.90  tff(c_468, plain, (v3_tops_1('#skF_5', '#skF_4') | ~v2_tops_1('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_303, c_466])).
% 4.45/1.90  tff(c_470, plain, (v3_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_326, c_468])).
% 4.45/1.90  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_470])).
% 4.45/1.90  tff(c_473, plain, (k2_tops_1('#skF_4', '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 4.45/1.90  tff(c_474, plain, (v3_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 4.45/1.90  tff(c_632, plain, (![B_152, A_153]: (v2_tops_1(B_152, A_153) | ~v3_tops_1(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.45/1.90  tff(c_635, plain, (v2_tops_1('#skF_5', '#skF_4') | ~v3_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_632])).
% 4.45/1.90  tff(c_638, plain, (v2_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_474, c_635])).
% 4.45/1.90  tff(c_744, plain, (![B_174, A_175]: (r1_tarski(B_174, k2_tops_1(A_175, B_174)) | ~v2_tops_1(B_174, A_175) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.45/1.90  tff(c_746, plain, (r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5')) | ~v2_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_744])).
% 4.45/1.90  tff(c_749, plain, (r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_638, c_746])).
% 4.45/1.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.90  tff(c_520, plain, (![A_133, B_134, C_135]: (k9_subset_1(A_133, B_134, C_135)=k3_xboole_0(B_134, C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.45/1.90  tff(c_523, plain, (![B_134]: (k9_subset_1(u1_struct_0('#skF_4'), B_134, '#skF_5')=k3_xboole_0(B_134, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_520])).
% 4.45/1.90  tff(c_575, plain, (![A_143, C_144, B_145]: (k9_subset_1(A_143, C_144, B_145)=k9_subset_1(A_143, B_145, C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.45/1.90  tff(c_577, plain, (![B_145]: (k9_subset_1(u1_struct_0('#skF_4'), B_145, '#skF_5')=k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_145))), inference(resolution, [status(thm)], [c_56, c_575])).
% 4.45/1.90  tff(c_579, plain, (![B_145]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_145)=k3_xboole_0(B_145, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_577])).
% 4.45/1.90  tff(c_666, plain, (![A_160, B_161]: (k2_pre_topc(A_160, B_161)=B_161 | ~v4_pre_topc(B_161, A_160) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.45/1.90  tff(c_669, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_666])).
% 4.45/1.90  tff(c_672, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_669])).
% 4.45/1.90  tff(c_1806, plain, (![A_320, B_321]: (k9_subset_1(u1_struct_0(A_320), k2_pre_topc(A_320, B_321), k2_pre_topc(A_320, k3_subset_1(u1_struct_0(A_320), B_321)))=k2_tops_1(A_320, B_321) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.45/1.90  tff(c_1815, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')))=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_672, c_1806])).
% 4.45/1.90  tff(c_1819, plain, (k3_xboole_0('#skF_5', k2_pre_topc('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')))=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2, c_579, c_1815])).
% 4.45/1.90  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.90  tff(c_490, plain, (![D_123, A_124, B_125]: (r2_hidden(D_123, A_124) | ~r2_hidden(D_123, k3_xboole_0(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.45/1.90  tff(c_597, plain, (![A_147, B_148, B_149]: (r2_hidden('#skF_1'(k3_xboole_0(A_147, B_148), B_149), A_147) | r1_tarski(k3_xboole_0(A_147, B_148), B_149))), inference(resolution, [status(thm)], [c_8, c_490])).
% 4.45/1.90  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.90  tff(c_622, plain, (![A_150, B_151]: (r1_tarski(k3_xboole_0(A_150, B_151), A_150))), inference(resolution, [status(thm)], [c_597, c_6])).
% 4.45/1.90  tff(c_639, plain, (![B_154, A_155]: (r1_tarski(k3_xboole_0(B_154, A_155), A_155))), inference(superposition, [status(thm), theory('equality')], [c_2, c_622])).
% 4.45/1.90  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.45/1.90  tff(c_659, plain, (![B_158, A_159]: (k3_xboole_0(B_158, A_159)=A_159 | ~r1_tarski(A_159, k3_xboole_0(B_158, A_159)))), inference(resolution, [status(thm)], [c_639, c_28])).
% 4.45/1.90  tff(c_665, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=A_1 | ~r1_tarski(A_1, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_659])).
% 4.45/1.90  tff(c_1904, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k3_subset_1(u1_struct_0('#skF_4'), '#skF_5')), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1819, c_665])).
% 4.45/1.90  tff(c_1958, plain, (k2_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_749, c_1819, c_2, c_1904])).
% 4.45/1.90  tff(c_1960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_473, c_1958])).
% 4.45/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.90  
% 4.45/1.90  Inference rules
% 4.45/1.90  ----------------------
% 4.45/1.90  #Ref     : 0
% 4.45/1.90  #Sup     : 468
% 4.45/1.90  #Fact    : 0
% 4.45/1.90  #Define  : 0
% 4.45/1.90  #Split   : 1
% 4.45/1.90  #Chain   : 0
% 4.45/1.90  #Close   : 0
% 4.45/1.90  
% 4.45/1.90  Ordering : KBO
% 4.45/1.90  
% 4.45/1.90  Simplification rules
% 4.45/1.90  ----------------------
% 4.45/1.90  #Subsume      : 121
% 4.45/1.90  #Demod        : 109
% 4.45/1.90  #Tautology    : 63
% 4.45/1.90  #SimpNegUnit  : 5
% 4.45/1.90  #BackRed      : 0
% 4.45/1.90  
% 4.45/1.90  #Partial instantiations: 0
% 4.45/1.90  #Strategies tried      : 1
% 4.45/1.90  
% 4.45/1.90  Timing (in seconds)
% 4.45/1.90  ----------------------
% 4.83/1.91  Preprocessing        : 0.41
% 4.83/1.91  Parsing              : 0.20
% 4.83/1.91  CNF conversion       : 0.03
% 4.83/1.91  Main loop            : 0.71
% 4.83/1.91  Inferencing          : 0.21
% 4.83/1.91  Reduction            : 0.22
% 4.83/1.91  Demodulation         : 0.17
% 4.83/1.91  BG Simplification    : 0.03
% 4.83/1.91  Subsumption          : 0.20
% 4.83/1.91  Abstraction          : 0.04
% 4.83/1.91  MUC search           : 0.00
% 4.83/1.91  Cooper               : 0.00
% 4.83/1.91  Total                : 1.16
% 4.83/1.91  Index Insertion      : 0.00
% 4.83/1.91  Index Deletion       : 0.00
% 4.83/1.91  Index Matching       : 0.00
% 4.83/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
