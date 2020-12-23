%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 281 expanded)
%              Number of leaves         :   33 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 ( 710 expanded)
%              Number of equality atoms :   51 ( 182 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_67])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_54])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61] :
      ( k9_subset_1(A_59,B_60,C_61) = k3_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    ! [B_60] : k9_subset_1(k2_struct_0('#skF_3'),B_60,'#skF_4') = k3_xboole_0(B_60,'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_138])).

tff(c_46,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_72,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46])).

tff(c_148,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_72])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_73,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_50])).

tff(c_80,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_73,c_80])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_483,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_1'(A_109,B_110,C_111),A_109)
      | r2_hidden('#skF_2'(A_109,B_110,C_111),C_111)
      | k3_xboole_0(A_109,B_110) = C_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_513,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_2'(A_109,B_110,A_109),A_109)
      | k3_xboole_0(A_109,B_110) = A_109 ) ),
    inference(resolution,[status(thm)],[c_483,c_14])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_538,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden('#skF_1'(A_114,B_115,C_116),A_114)
      | ~ r2_hidden('#skF_2'(A_114,B_115,C_116),B_115)
      | ~ r2_hidden('#skF_2'(A_114,B_115,C_116),A_114)
      | k3_xboole_0(A_114,B_115) = C_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_555,plain,(
    ! [A_1,C_3] :
      ( ~ r2_hidden('#skF_2'(A_1,C_3,C_3),A_1)
      | r2_hidden('#skF_1'(A_1,C_3,C_3),A_1)
      | k3_xboole_0(A_1,C_3) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_538])).

tff(c_602,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r2_hidden('#skF_1'(A_122,B_123,C_124),C_124)
      | ~ r2_hidden('#skF_2'(A_122,B_123,C_124),B_123)
      | ~ r2_hidden('#skF_2'(A_122,B_123,C_124),A_122)
      | k3_xboole_0(A_122,B_123) = C_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_619,plain,(
    ! [A_125] :
      ( ~ r2_hidden('#skF_2'(A_125,A_125,A_125),A_125)
      | k3_xboole_0(A_125,A_125) = A_125 ) ),
    inference(resolution,[status(thm)],[c_555,c_602])).

tff(c_645,plain,(
    ! [B_110] : k3_xboole_0(B_110,B_110) = B_110 ),
    inference(resolution,[status(thm)],[c_513,c_619])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_521,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_2'(A_112,B_113,A_112),A_112)
      | k3_xboole_0(A_112,B_113) = A_112 ) ),
    inference(resolution,[status(thm)],[c_483,c_14])).

tff(c_28,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_559,plain,(
    ! [A_117,B_118,A_119] :
      ( r2_hidden('#skF_2'(A_117,B_118,A_117),A_119)
      | ~ m1_subset_1(A_117,k1_zfmisc_1(A_119))
      | k3_xboole_0(A_117,B_118) = A_117 ) ),
    inference(resolution,[status(thm)],[c_521,c_28])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1092,plain,(
    ! [A_171,B_172,B_173,A_174] :
      ( r2_hidden('#skF_2'(A_171,B_172,A_171),B_173)
      | ~ m1_subset_1(A_171,k1_zfmisc_1(k3_xboole_0(A_174,B_173)))
      | k3_xboole_0(A_171,B_172) = A_171 ) ),
    inference(resolution,[status(thm)],[c_559,c_4])).

tff(c_1191,plain,(
    ! [A_182,B_183,B_184,A_185] :
      ( r2_hidden('#skF_2'(A_182,B_183,A_182),B_184)
      | k3_xboole_0(A_182,B_183) = A_182
      | ~ r1_tarski(A_182,k3_xboole_0(A_185,B_184)) ) ),
    inference(resolution,[status(thm)],[c_34,c_1092])).

tff(c_1195,plain,(
    ! [A_182,B_183,B_110] :
      ( r2_hidden('#skF_2'(A_182,B_183,A_182),B_110)
      | k3_xboole_0(A_182,B_183) = A_182
      | ~ r1_tarski(A_182,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_1191])).

tff(c_1200,plain,(
    ! [A_186,B_187,B_188] :
      ( r2_hidden('#skF_2'(A_186,B_187,A_186),B_188)
      | k3_xboole_0(A_186,B_187) = A_186
      | ~ r1_tarski(A_186,B_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_1191])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4320,plain,(
    ! [A_495,B_496] :
      ( r2_hidden('#skF_1'(A_495,B_496,A_495),A_495)
      | ~ r2_hidden('#skF_2'(A_495,B_496,A_495),A_495)
      | k3_xboole_0(A_495,B_496) = A_495
      | ~ r1_tarski(A_495,B_496) ) ),
    inference(resolution,[status(thm)],[c_1200,c_12])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4384,plain,(
    ! [A_499,B_500] :
      ( ~ r2_hidden('#skF_2'(A_499,B_500,A_499),B_500)
      | ~ r2_hidden('#skF_2'(A_499,B_500,A_499),A_499)
      | k3_xboole_0(A_499,B_500) = A_499
      | ~ r1_tarski(A_499,B_500) ) ),
    inference(resolution,[status(thm)],[c_4320,c_8])).

tff(c_4619,plain,(
    ! [A_501,B_502] :
      ( ~ r2_hidden('#skF_2'(A_501,B_502,A_501),A_501)
      | k3_xboole_0(A_501,B_502) = A_501
      | ~ r1_tarski(A_501,B_502) ) ),
    inference(resolution,[status(thm)],[c_1195,c_4384])).

tff(c_4761,plain,(
    ! [B_110,B_183] :
      ( ~ r1_tarski(B_110,B_183)
      | k3_xboole_0(B_110,B_183) = B_110
      | ~ r1_tarski(B_110,B_110) ) ),
    inference(resolution,[status(thm)],[c_1195,c_4619])).

tff(c_4883,plain,(
    ! [B_503,B_504] :
      ( ~ r1_tarski(B_503,B_504)
      | k3_xboole_0(B_503,B_504) = B_503 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4761])).

tff(c_4893,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_92,c_4883])).

tff(c_48,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_168,plain,(
    ! [B_64,B_65,A_66] :
      ( k9_subset_1(B_64,B_65,A_66) = k3_xboole_0(B_65,A_66)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_179,plain,(
    ! [B_8,B_65] : k9_subset_1(B_8,B_65,B_8) = k3_xboole_0(B_65,B_8) ),
    inference(resolution,[status(thm)],[c_24,c_168])).

tff(c_52,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_258,plain,(
    ! [A_76,B_77] :
      ( k2_pre_topc(A_76,B_77) = k2_struct_0(A_76)
      | ~ v1_tops_1(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,(
    ! [B_77] :
      ( k2_pre_topc('#skF_3',B_77) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_77,'#skF_3')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_258])).

tff(c_269,plain,(
    ! [B_78] :
      ( k2_pre_topc('#skF_3',B_78) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_78,'#skF_3')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_265])).

tff(c_276,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_269])).

tff(c_283,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_276])).

tff(c_785,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_pre_topc(A_133,k9_subset_1(u1_struct_0(A_133),B_134,k2_pre_topc(A_133,C_135))) = k2_pre_topc(A_133,k9_subset_1(u1_struct_0(A_133),B_134,C_135))
      | ~ v3_pre_topc(B_134,A_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_800,plain,(
    ! [B_134] :
      ( k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_134,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_134,'#skF_4'))
      | ~ v3_pre_topc(B_134,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_785])).

tff(c_3993,plain,(
    ! [B_488] :
      ( k2_pre_topc('#skF_3',k3_xboole_0(B_488,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0(B_488,'#skF_4'))
      | ~ v3_pre_topc(B_488,'#skF_3')
      | ~ m1_subset_1(B_488,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_71,c_74,c_71,c_179,c_146,c_71,c_71,c_800])).

tff(c_4003,plain,
    ( k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_3993])).

tff(c_4009,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4003])).

tff(c_5091,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4893,c_4009])).

tff(c_5093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.57  
% 7.21/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.58  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 7.21/2.58  
% 7.21/2.58  %Foreground sorts:
% 7.21/2.58  
% 7.21/2.58  
% 7.21/2.58  %Background operators:
% 7.21/2.58  
% 7.21/2.58  
% 7.21/2.58  %Foreground operators:
% 7.21/2.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.21/2.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.21/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.21/2.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.21/2.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.21/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.58  tff('#skF_5', type, '#skF_5': $i).
% 7.21/2.58  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.21/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.21/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.21/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.21/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.21/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.21/2.58  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.21/2.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.21/2.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.21/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.58  
% 7.21/2.59  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 7.21/2.59  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.21/2.59  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.21/2.59  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.21/2.59  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.21/2.59  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.21/2.59  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.21/2.59  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.21/2.59  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 7.21/2.59  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 7.21/2.59  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_38, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.21/2.59  tff(c_62, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.21/2.59  tff(c_67, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_38, c_62])).
% 7.21/2.59  tff(c_71, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_67])).
% 7.21/2.59  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_54])).
% 7.21/2.59  tff(c_138, plain, (![A_59, B_60, C_61]: (k9_subset_1(A_59, B_60, C_61)=k3_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.59  tff(c_146, plain, (![B_60]: (k9_subset_1(k2_struct_0('#skF_3'), B_60, '#skF_4')=k3_xboole_0(B_60, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_138])).
% 7.21/2.59  tff(c_46, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_72, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46])).
% 7.21/2.59  tff(c_148, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_72])).
% 7.21/2.59  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_73, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_50])).
% 7.21/2.59  tff(c_80, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.21/2.59  tff(c_92, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_73, c_80])).
% 7.21/2.59  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.21/2.59  tff(c_483, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_1'(A_109, B_110, C_111), A_109) | r2_hidden('#skF_2'(A_109, B_110, C_111), C_111) | k3_xboole_0(A_109, B_110)=C_111)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_513, plain, (![A_109, B_110]: (r2_hidden('#skF_2'(A_109, B_110, A_109), A_109) | k3_xboole_0(A_109, B_110)=A_109)), inference(resolution, [status(thm)], [c_483, c_14])).
% 7.21/2.59  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_538, plain, (![A_114, B_115, C_116]: (r2_hidden('#skF_1'(A_114, B_115, C_116), A_114) | ~r2_hidden('#skF_2'(A_114, B_115, C_116), B_115) | ~r2_hidden('#skF_2'(A_114, B_115, C_116), A_114) | k3_xboole_0(A_114, B_115)=C_116)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_555, plain, (![A_1, C_3]: (~r2_hidden('#skF_2'(A_1, C_3, C_3), A_1) | r2_hidden('#skF_1'(A_1, C_3, C_3), A_1) | k3_xboole_0(A_1, C_3)=C_3)), inference(resolution, [status(thm)], [c_18, c_538])).
% 7.21/2.59  tff(c_602, plain, (![A_122, B_123, C_124]: (~r2_hidden('#skF_1'(A_122, B_123, C_124), C_124) | ~r2_hidden('#skF_2'(A_122, B_123, C_124), B_123) | ~r2_hidden('#skF_2'(A_122, B_123, C_124), A_122) | k3_xboole_0(A_122, B_123)=C_124)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_619, plain, (![A_125]: (~r2_hidden('#skF_2'(A_125, A_125, A_125), A_125) | k3_xboole_0(A_125, A_125)=A_125)), inference(resolution, [status(thm)], [c_555, c_602])).
% 7.21/2.59  tff(c_645, plain, (![B_110]: (k3_xboole_0(B_110, B_110)=B_110)), inference(resolution, [status(thm)], [c_513, c_619])).
% 7.21/2.59  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.21/2.59  tff(c_521, plain, (![A_112, B_113]: (r2_hidden('#skF_2'(A_112, B_113, A_112), A_112) | k3_xboole_0(A_112, B_113)=A_112)), inference(resolution, [status(thm)], [c_483, c_14])).
% 7.21/2.59  tff(c_28, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.21/2.59  tff(c_559, plain, (![A_117, B_118, A_119]: (r2_hidden('#skF_2'(A_117, B_118, A_117), A_119) | ~m1_subset_1(A_117, k1_zfmisc_1(A_119)) | k3_xboole_0(A_117, B_118)=A_117)), inference(resolution, [status(thm)], [c_521, c_28])).
% 7.21/2.59  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_1092, plain, (![A_171, B_172, B_173, A_174]: (r2_hidden('#skF_2'(A_171, B_172, A_171), B_173) | ~m1_subset_1(A_171, k1_zfmisc_1(k3_xboole_0(A_174, B_173))) | k3_xboole_0(A_171, B_172)=A_171)), inference(resolution, [status(thm)], [c_559, c_4])).
% 7.21/2.59  tff(c_1191, plain, (![A_182, B_183, B_184, A_185]: (r2_hidden('#skF_2'(A_182, B_183, A_182), B_184) | k3_xboole_0(A_182, B_183)=A_182 | ~r1_tarski(A_182, k3_xboole_0(A_185, B_184)))), inference(resolution, [status(thm)], [c_34, c_1092])).
% 7.21/2.59  tff(c_1195, plain, (![A_182, B_183, B_110]: (r2_hidden('#skF_2'(A_182, B_183, A_182), B_110) | k3_xboole_0(A_182, B_183)=A_182 | ~r1_tarski(A_182, B_110))), inference(superposition, [status(thm), theory('equality')], [c_645, c_1191])).
% 7.21/2.59  tff(c_1200, plain, (![A_186, B_187, B_188]: (r2_hidden('#skF_2'(A_186, B_187, A_186), B_188) | k3_xboole_0(A_186, B_187)=A_186 | ~r1_tarski(A_186, B_188))), inference(superposition, [status(thm), theory('equality')], [c_645, c_1191])).
% 7.21/2.59  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_4320, plain, (![A_495, B_496]: (r2_hidden('#skF_1'(A_495, B_496, A_495), A_495) | ~r2_hidden('#skF_2'(A_495, B_496, A_495), A_495) | k3_xboole_0(A_495, B_496)=A_495 | ~r1_tarski(A_495, B_496))), inference(resolution, [status(thm)], [c_1200, c_12])).
% 7.21/2.59  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.59  tff(c_4384, plain, (![A_499, B_500]: (~r2_hidden('#skF_2'(A_499, B_500, A_499), B_500) | ~r2_hidden('#skF_2'(A_499, B_500, A_499), A_499) | k3_xboole_0(A_499, B_500)=A_499 | ~r1_tarski(A_499, B_500))), inference(resolution, [status(thm)], [c_4320, c_8])).
% 7.21/2.59  tff(c_4619, plain, (![A_501, B_502]: (~r2_hidden('#skF_2'(A_501, B_502, A_501), A_501) | k3_xboole_0(A_501, B_502)=A_501 | ~r1_tarski(A_501, B_502))), inference(resolution, [status(thm)], [c_1195, c_4384])).
% 7.21/2.59  tff(c_4761, plain, (![B_110, B_183]: (~r1_tarski(B_110, B_183) | k3_xboole_0(B_110, B_183)=B_110 | ~r1_tarski(B_110, B_110))), inference(resolution, [status(thm)], [c_1195, c_4619])).
% 7.21/2.59  tff(c_4883, plain, (![B_503, B_504]: (~r1_tarski(B_503, B_504) | k3_xboole_0(B_503, B_504)=B_503)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4761])).
% 7.21/2.59  tff(c_4893, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(resolution, [status(thm)], [c_92, c_4883])).
% 7.21/2.59  tff(c_48, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_168, plain, (![B_64, B_65, A_66]: (k9_subset_1(B_64, B_65, A_66)=k3_xboole_0(B_65, A_66) | ~r1_tarski(A_66, B_64))), inference(resolution, [status(thm)], [c_34, c_138])).
% 7.21/2.59  tff(c_179, plain, (![B_8, B_65]: (k9_subset_1(B_8, B_65, B_8)=k3_xboole_0(B_65, B_8))), inference(resolution, [status(thm)], [c_24, c_168])).
% 7.21/2.59  tff(c_52, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_258, plain, (![A_76, B_77]: (k2_pre_topc(A_76, B_77)=k2_struct_0(A_76) | ~v1_tops_1(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.21/2.59  tff(c_265, plain, (![B_77]: (k2_pre_topc('#skF_3', B_77)=k2_struct_0('#skF_3') | ~v1_tops_1(B_77, '#skF_3') | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_258])).
% 7.21/2.59  tff(c_269, plain, (![B_78]: (k2_pre_topc('#skF_3', B_78)=k2_struct_0('#skF_3') | ~v1_tops_1(B_78, '#skF_3') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_265])).
% 7.21/2.59  tff(c_276, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_269])).
% 7.21/2.59  tff(c_283, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_276])).
% 7.21/2.59  tff(c_785, plain, (![A_133, B_134, C_135]: (k2_pre_topc(A_133, k9_subset_1(u1_struct_0(A_133), B_134, k2_pre_topc(A_133, C_135)))=k2_pre_topc(A_133, k9_subset_1(u1_struct_0(A_133), B_134, C_135)) | ~v3_pre_topc(B_134, A_133) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.21/2.59  tff(c_800, plain, (![B_134]: (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_134, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_134, '#skF_4')) | ~v3_pre_topc(B_134, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_785])).
% 7.21/2.59  tff(c_3993, plain, (![B_488]: (k2_pre_topc('#skF_3', k3_xboole_0(B_488, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0(B_488, '#skF_4')) | ~v3_pre_topc(B_488, '#skF_3') | ~m1_subset_1(B_488, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_71, c_74, c_71, c_179, c_146, c_71, c_71, c_800])).
% 7.21/2.59  tff(c_4003, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_73, c_3993])).
% 7.21/2.59  tff(c_4009, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4003])).
% 7.21/2.59  tff(c_5091, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4893, c_4009])).
% 7.21/2.59  tff(c_5093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_5091])).
% 7.21/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.59  
% 7.21/2.59  Inference rules
% 7.21/2.59  ----------------------
% 7.21/2.59  #Ref     : 0
% 7.21/2.59  #Sup     : 1198
% 7.21/2.59  #Fact    : 0
% 7.21/2.59  #Define  : 0
% 7.21/2.59  #Split   : 6
% 7.21/2.59  #Chain   : 0
% 7.21/2.59  #Close   : 0
% 7.21/2.59  
% 7.21/2.59  Ordering : KBO
% 7.21/2.59  
% 7.21/2.59  Simplification rules
% 7.21/2.59  ----------------------
% 7.21/2.59  #Subsume      : 255
% 7.21/2.60  #Demod        : 413
% 7.21/2.60  #Tautology    : 117
% 7.21/2.60  #SimpNegUnit  : 6
% 7.21/2.60  #BackRed      : 5
% 7.21/2.60  
% 7.21/2.60  #Partial instantiations: 0
% 7.21/2.60  #Strategies tried      : 1
% 7.21/2.60  
% 7.21/2.60  Timing (in seconds)
% 7.21/2.60  ----------------------
% 7.21/2.60  Preprocessing        : 0.35
% 7.21/2.60  Parsing              : 0.18
% 7.21/2.60  CNF conversion       : 0.03
% 7.21/2.60  Main loop            : 1.44
% 7.21/2.60  Inferencing          : 0.42
% 7.21/2.60  Reduction            : 0.35
% 7.21/2.60  Demodulation         : 0.24
% 7.21/2.60  BG Simplification    : 0.05
% 7.21/2.60  Subsumption          : 0.50
% 7.21/2.60  Abstraction          : 0.09
% 7.21/2.60  MUC search           : 0.00
% 7.21/2.60  Cooper               : 0.00
% 7.21/2.60  Total                : 1.82
% 7.21/2.60  Index Insertion      : 0.00
% 7.21/2.60  Index Deletion       : 0.00
% 7.21/2.60  Index Matching       : 0.00
% 7.21/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
