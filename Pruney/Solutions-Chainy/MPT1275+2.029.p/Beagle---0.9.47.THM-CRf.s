%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:05 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 200 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  151 ( 488 expanded)
%              Number of equality atoms :   32 ( 102 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_52,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_57,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_63,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_46])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_386,plain,(
    ! [A_82,B_83] :
      ( k1_tops_1(A_82,B_83) = k1_xboole_0
      | ~ v2_tops_1(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_397,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_386])).

tff(c_406,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_397])).

tff(c_408,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_625,plain,(
    ! [B_106,A_107] :
      ( v2_tops_1(B_106,A_107)
      | ~ r1_tarski(B_106,k2_tops_1(A_107,B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_630,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_625])).

tff(c_635,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6,c_630])).

tff(c_637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_635])).

tff(c_639,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_40,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_930,plain,(
    ! [B_139,A_140] :
      ( v3_tops_1(B_139,A_140)
      | ~ v4_pre_topc(B_139,A_140)
      | ~ v2_tops_1(B_139,A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_941,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_930])).

tff(c_950,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_639,c_40,c_941])).

tff(c_952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_950])).

tff(c_954,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_953,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1209,plain,(
    ! [B_179,A_180] :
      ( v2_tops_1(B_179,A_180)
      | ~ v3_tops_1(B_179,A_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1220,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1209])).

tff(c_1229,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_953,c_1220])).

tff(c_1476,plain,(
    ! [B_203,A_204] :
      ( r1_tarski(B_203,k2_tops_1(A_204,B_203))
      | ~ v2_tops_1(B_203,A_204)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1484,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1476])).

tff(c_1492,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1229,c_1484])).

tff(c_1076,plain,(
    ! [A_162,B_163] :
      ( k4_xboole_0(A_162,B_163) = k3_subset_1(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1092,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_subset_1(A_10,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_1076])).

tff(c_1249,plain,(
    ! [A_183,B_184] :
      ( k1_tops_1(A_183,B_184) = k1_xboole_0
      | ~ v2_tops_1(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1260,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1249])).

tff(c_1269,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1229,c_1260])).

tff(c_1125,plain,(
    ! [A_167,B_168,C_169] :
      ( k7_subset_1(A_167,B_168,C_169) = k4_xboole_0(B_168,C_169)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1136,plain,(
    ! [C_169] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_169) = k4_xboole_0('#skF_2',C_169) ),
    inference(resolution,[status(thm)],[c_42,c_1125])).

tff(c_1315,plain,(
    ! [A_190,B_191] :
      ( k2_pre_topc(A_190,B_191) = B_191
      | ~ v4_pre_topc(B_191,A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1326,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1315])).

tff(c_1335,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_1326])).

tff(c_1762,plain,(
    ! [A_231,B_232] :
      ( k7_subset_1(u1_struct_0(A_231),k2_pre_topc(A_231,B_232),k1_tops_1(A_231,B_232)) = k2_tops_1(A_231,B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1774,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_1762])).

tff(c_1783,plain,(
    k3_subset_1('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1092,c_1269,c_1136,c_1774])).

tff(c_998,plain,(
    ! [A_147,B_148] :
      ( m1_subset_1(k3_subset_1(A_147,B_148),k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1003,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(k3_subset_1(A_149,B_150),A_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_998,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1011,plain,(
    ! [A_149,B_150] :
      ( k3_subset_1(A_149,B_150) = A_149
      | ~ r1_tarski(A_149,k3_subset_1(A_149,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_1003,c_2])).

tff(c_1795,plain,
    ( k3_subset_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1783,c_1011])).

tff(c_1811,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1492,c_1783,c_1795])).

tff(c_1813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_1811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.71  
% 3.27/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.71  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.27/1.71  
% 3.27/1.71  %Foreground sorts:
% 3.27/1.71  
% 3.27/1.71  
% 3.27/1.71  %Background operators:
% 3.27/1.71  
% 3.27/1.71  
% 3.27/1.71  %Foreground operators:
% 3.27/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.71  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.27/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.71  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.27/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.71  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.27/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.27/1.71  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.27/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.71  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.27/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.71  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.27/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.27/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.71  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.27/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.71  
% 3.27/1.73  tff(f_127, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.27/1.73  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.27/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.27/1.73  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.27/1.73  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 3.27/1.73  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.27/1.73  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.27/1.73  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.27/1.73  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.27/1.73  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.27/1.73  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.27/1.73  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.27/1.73  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.27/1.73  tff(c_52, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.73  tff(c_57, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 3.27/1.73  tff(c_46, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.73  tff(c_63, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_46])).
% 3.27/1.73  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.73  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.73  tff(c_386, plain, (![A_82, B_83]: (k1_tops_1(A_82, B_83)=k1_xboole_0 | ~v2_tops_1(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.27/1.73  tff(c_397, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_386])).
% 3.27/1.73  tff(c_406, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_397])).
% 3.27/1.73  tff(c_408, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_406])).
% 3.27/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.73  tff(c_625, plain, (![B_106, A_107]: (v2_tops_1(B_106, A_107) | ~r1_tarski(B_106, k2_tops_1(A_107, B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.27/1.73  tff(c_630, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_625])).
% 3.27/1.73  tff(c_635, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6, c_630])).
% 3.27/1.73  tff(c_637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_635])).
% 3.27/1.73  tff(c_639, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_406])).
% 3.27/1.73  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.27/1.73  tff(c_930, plain, (![B_139, A_140]: (v3_tops_1(B_139, A_140) | ~v4_pre_topc(B_139, A_140) | ~v2_tops_1(B_139, A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.27/1.73  tff(c_941, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_930])).
% 3.27/1.73  tff(c_950, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_639, c_40, c_941])).
% 3.27/1.73  tff(c_952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_950])).
% 3.27/1.73  tff(c_954, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 3.27/1.73  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.73  tff(c_953, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 3.27/1.73  tff(c_1209, plain, (![B_179, A_180]: (v2_tops_1(B_179, A_180) | ~v3_tops_1(B_179, A_180) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.27/1.73  tff(c_1220, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1209])).
% 3.27/1.73  tff(c_1229, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_953, c_1220])).
% 3.27/1.73  tff(c_1476, plain, (![B_203, A_204]: (r1_tarski(B_203, k2_tops_1(A_204, B_203)) | ~v2_tops_1(B_203, A_204) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.27/1.73  tff(c_1484, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1476])).
% 3.27/1.73  tff(c_1492, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1229, c_1484])).
% 3.27/1.73  tff(c_1076, plain, (![A_162, B_163]: (k4_xboole_0(A_162, B_163)=k3_subset_1(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(A_162)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.73  tff(c_1092, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_subset_1(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1076])).
% 3.27/1.73  tff(c_1249, plain, (![A_183, B_184]: (k1_tops_1(A_183, B_184)=k1_xboole_0 | ~v2_tops_1(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.27/1.73  tff(c_1260, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1249])).
% 3.27/1.73  tff(c_1269, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1229, c_1260])).
% 3.27/1.73  tff(c_1125, plain, (![A_167, B_168, C_169]: (k7_subset_1(A_167, B_168, C_169)=k4_xboole_0(B_168, C_169) | ~m1_subset_1(B_168, k1_zfmisc_1(A_167)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.73  tff(c_1136, plain, (![C_169]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_169)=k4_xboole_0('#skF_2', C_169))), inference(resolution, [status(thm)], [c_42, c_1125])).
% 3.27/1.73  tff(c_1315, plain, (![A_190, B_191]: (k2_pre_topc(A_190, B_191)=B_191 | ~v4_pre_topc(B_191, A_190) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.73  tff(c_1326, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1315])).
% 3.27/1.73  tff(c_1335, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_1326])).
% 3.27/1.73  tff(c_1762, plain, (![A_231, B_232]: (k7_subset_1(u1_struct_0(A_231), k2_pre_topc(A_231, B_232), k1_tops_1(A_231, B_232))=k2_tops_1(A_231, B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.27/1.73  tff(c_1774, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1335, c_1762])).
% 3.27/1.73  tff(c_1783, plain, (k3_subset_1('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1092, c_1269, c_1136, c_1774])).
% 3.27/1.73  tff(c_998, plain, (![A_147, B_148]: (m1_subset_1(k3_subset_1(A_147, B_148), k1_zfmisc_1(A_147)) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.73  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.73  tff(c_1003, plain, (![A_149, B_150]: (r1_tarski(k3_subset_1(A_149, B_150), A_149) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(resolution, [status(thm)], [c_998, c_16])).
% 3.27/1.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.73  tff(c_1011, plain, (![A_149, B_150]: (k3_subset_1(A_149, B_150)=A_149 | ~r1_tarski(A_149, k3_subset_1(A_149, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(resolution, [status(thm)], [c_1003, c_2])).
% 3.27/1.73  tff(c_1795, plain, (k3_subset_1('#skF_2', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1783, c_1011])).
% 3.27/1.73  tff(c_1811, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1492, c_1783, c_1795])).
% 3.27/1.73  tff(c_1813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_954, c_1811])).
% 3.27/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.73  
% 3.27/1.73  Inference rules
% 3.27/1.73  ----------------------
% 3.27/1.73  #Ref     : 0
% 3.27/1.73  #Sup     : 376
% 3.27/1.73  #Fact    : 0
% 3.27/1.73  #Define  : 0
% 3.27/1.73  #Split   : 4
% 3.27/1.73  #Chain   : 0
% 3.27/1.73  #Close   : 0
% 3.27/1.73  
% 3.27/1.73  Ordering : KBO
% 3.27/1.73  
% 3.27/1.73  Simplification rules
% 3.27/1.73  ----------------------
% 3.27/1.73  #Subsume      : 44
% 3.27/1.73  #Demod        : 224
% 3.27/1.73  #Tautology    : 183
% 3.27/1.73  #SimpNegUnit  : 7
% 3.27/1.73  #BackRed      : 0
% 3.27/1.73  
% 3.27/1.73  #Partial instantiations: 0
% 3.27/1.73  #Strategies tried      : 1
% 3.27/1.73  
% 3.27/1.73  Timing (in seconds)
% 3.27/1.73  ----------------------
% 3.27/1.73  Preprocessing        : 0.30
% 3.27/1.73  Parsing              : 0.15
% 3.27/1.73  CNF conversion       : 0.02
% 3.27/1.73  Main loop            : 0.48
% 3.27/1.73  Inferencing          : 0.18
% 3.27/1.73  Reduction            : 0.15
% 3.27/1.73  Demodulation         : 0.10
% 3.27/1.73  BG Simplification    : 0.02
% 3.27/1.73  Subsumption          : 0.08
% 3.27/1.73  Abstraction          : 0.03
% 3.27/1.73  MUC search           : 0.00
% 3.27/1.73  Cooper               : 0.00
% 3.27/1.73  Total                : 0.81
% 3.27/1.73  Index Insertion      : 0.00
% 3.27/1.73  Index Deletion       : 0.00
% 3.27/1.73  Index Matching       : 0.00
% 3.27/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
