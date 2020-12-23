%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 252 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 588 expanded)
%              Number of equality atoms :   52 ( 150 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_107,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_110,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_48])).

tff(c_148,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,C_55) = k3_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [B_54] : k9_subset_1(k2_struct_0('#skF_3'),B_54,'#skF_4') = k3_xboole_0(B_54,'#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_148])).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_108,plain,(
    k2_pre_topc('#skF_3',k9_subset_1(k2_struct_0('#skF_3'),'#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_40])).

tff(c_178,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_108])).

tff(c_179,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) != k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_22,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_303,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(A_75,B_76,C_77),B_76)
      | r2_hidden('#skF_2'(A_75,B_76,C_77),C_77)
      | k3_xboole_0(A_75,B_76) = C_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_624,plain,(
    ! [A_117,B_118,C_119,A_120] :
      ( r2_hidden('#skF_1'(A_117,B_118,C_119),A_120)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_120))
      | r2_hidden('#skF_2'(A_117,B_118,C_119),C_119)
      | k3_xboole_0(A_117,B_118) = C_119 ) ),
    inference(resolution,[status(thm)],[c_303,c_26])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_668,plain,(
    ! [B_121,A_122,A_123] :
      ( ~ m1_subset_1(B_121,k1_zfmisc_1(A_122))
      | r2_hidden('#skF_2'(A_123,B_121,A_122),A_122)
      | k3_xboole_0(A_123,B_121) = A_122 ) ),
    inference(resolution,[status(thm)],[c_624,c_16])).

tff(c_689,plain,(
    ! [A_123,B_121,A_122,A_11] :
      ( r2_hidden('#skF_2'(A_123,B_121,A_122),A_11)
      | ~ m1_subset_1(A_122,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_122))
      | k3_xboole_0(A_123,B_121) = A_122 ) ),
    inference(resolution,[status(thm)],[c_668,c_26])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_109,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_44])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_330,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79,C_80),C_80)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k3_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_359,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_2'(A_84,B_85,B_85),B_85)
      | k3_xboole_0(A_84,B_85) = B_85 ) ),
    inference(resolution,[status(thm)],[c_18,c_330])).

tff(c_387,plain,(
    ! [A_88,B_89,A_90] :
      ( r2_hidden('#skF_2'(A_88,B_89,B_89),A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | k3_xboole_0(A_88,B_89) = B_89 ) ),
    inference(resolution,[status(thm)],[c_359,c_26])).

tff(c_952,plain,(
    ! [A_153,B_154,A_155,A_156] :
      ( r2_hidden('#skF_2'(A_153,B_154,B_154),A_155)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_156))
      | k3_xboole_0(A_153,B_154) = B_154 ) ),
    inference(resolution,[status(thm)],[c_387,c_26])).

tff(c_960,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_2'(A_153,B_154,B_154),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_154,k1_zfmisc_1('#skF_5'))
      | k3_xboole_0(A_153,B_154) = B_154 ) ),
    inference(resolution,[status(thm)],[c_109,c_952])).

tff(c_974,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_2'(A_159,B_160,B_160),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_160,k1_zfmisc_1('#skF_5'))
      | k3_xboole_0(A_159,B_160) = B_160 ) ),
    inference(resolution,[status(thm)],[c_109,c_952])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2311,plain,(
    ! [B_292] :
      ( r2_hidden('#skF_1'(k2_struct_0('#skF_3'),B_292,B_292),B_292)
      | ~ r2_hidden('#skF_2'(k2_struct_0('#skF_3'),B_292,B_292),B_292)
      | ~ m1_subset_1(B_292,k1_zfmisc_1('#skF_5'))
      | k3_xboole_0(k2_struct_0('#skF_3'),B_292) = B_292 ) ),
    inference(resolution,[status(thm)],[c_974,c_12])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2578,plain,(
    ! [B_311] :
      ( ~ r2_hidden('#skF_2'(k2_struct_0('#skF_3'),B_311,B_311),k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_2'(k2_struct_0('#skF_3'),B_311,B_311),B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1('#skF_5'))
      | k3_xboole_0(k2_struct_0('#skF_3'),B_311) = B_311 ) ),
    inference(resolution,[status(thm)],[c_2311,c_10])).

tff(c_2816,plain,(
    ! [B_322] :
      ( ~ r2_hidden('#skF_2'(k2_struct_0('#skF_3'),B_322,B_322),B_322)
      | ~ m1_subset_1(B_322,k1_zfmisc_1('#skF_5'))
      | k3_xboole_0(k2_struct_0('#skF_3'),B_322) = B_322 ) ),
    inference(resolution,[status(thm)],[c_960,c_2578])).

tff(c_2840,plain,(
    ! [A_11] :
      ( ~ m1_subset_1(A_11,k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(A_11,k1_zfmisc_1(A_11))
      | k3_xboole_0(k2_struct_0('#skF_3'),A_11) = A_11 ) ),
    inference(resolution,[status(thm)],[c_689,c_2816])).

tff(c_2933,plain,(
    ! [A_323] :
      ( ~ m1_subset_1(A_323,k1_zfmisc_1('#skF_5'))
      | k3_xboole_0(k2_struct_0('#skF_3'),A_323) = A_323 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2840])).

tff(c_2938,plain,(
    k3_xboole_0(k2_struct_0('#skF_3'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53,c_2933])).

tff(c_3143,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_3')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2938,c_2])).

tff(c_42,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_157,plain,(
    ! [A_10,B_54] : k9_subset_1(A_10,B_54,A_10) = k3_xboole_0(B_54,A_10) ),
    inference(resolution,[status(thm)],[c_53,c_148])).

tff(c_46,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_167,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = k2_struct_0(A_58)
      | ~ v1_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_170,plain,(
    ! [B_59] :
      ( k2_pre_topc('#skF_3',B_59) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_59,'#skF_3')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_167])).

tff(c_198,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_3',B_62) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_62,'#skF_3')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_170])).

tff(c_201,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_198])).

tff(c_211,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_201])).

tff(c_576,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_pre_topc(A_106,k9_subset_1(u1_struct_0(A_106),B_107,k2_pre_topc(A_106,C_108))) = k2_pre_topc(A_106,k9_subset_1(u1_struct_0(A_106),B_107,C_108))
      | ~ v3_pre_topc(B_107,A_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_591,plain,(
    ! [B_107] :
      ( k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_107,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_107,'#skF_4'))
      | ~ v3_pre_topc(B_107,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_576])).

tff(c_2480,plain,(
    ! [B_306] :
      ( k2_pre_topc('#skF_3',k3_xboole_0(B_306,k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0(B_306,'#skF_4'))
      | ~ v3_pre_topc(B_306,'#skF_3')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_107,c_110,c_107,c_155,c_157,c_107,c_107,c_591])).

tff(c_2486,plain,
    ( k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_5','#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_2480])).

tff(c_2495,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_5',k2_struct_0('#skF_3'))) = k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2,c_2486])).

tff(c_3201,plain,(
    k2_pre_topc('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k2_pre_topc('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3143,c_2495])).

tff(c_3203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_3201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.18  
% 5.76/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.18  %$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.76/2.18  
% 5.76/2.18  %Foreground sorts:
% 5.76/2.18  
% 5.76/2.18  
% 5.76/2.18  %Background operators:
% 5.76/2.18  
% 5.76/2.18  
% 5.76/2.18  %Foreground operators:
% 5.76/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.76/2.18  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.76/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.76/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.76/2.18  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.76/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.76/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.76/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.76/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.76/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.76/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.76/2.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.76/2.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.76/2.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.76/2.18  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.76/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.18  
% 5.76/2.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.76/2.19  tff(f_99, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 5.76/2.19  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.76/2.19  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.76/2.19  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.76/2.19  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.76/2.19  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.76/2.19  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.76/2.19  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.76/2.19  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 5.76/2.19  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 5.76/2.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.76/2.19  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_32, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.76/2.19  tff(c_98, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.76/2.19  tff(c_103, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_32, c_98])).
% 5.76/2.19  tff(c_107, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_103])).
% 5.76/2.19  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_110, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_48])).
% 5.76/2.19  tff(c_148, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, C_55)=k3_xboole_0(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.76/2.19  tff(c_155, plain, (![B_54]: (k9_subset_1(k2_struct_0('#skF_3'), B_54, '#skF_4')=k3_xboole_0(B_54, '#skF_4'))), inference(resolution, [status(thm)], [c_110, c_148])).
% 5.76/2.19  tff(c_40, plain, (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_108, plain, (k2_pre_topc('#skF_3', k9_subset_1(k2_struct_0('#skF_3'), '#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_40])).
% 5.76/2.19  tff(c_178, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_108])).
% 5.76/2.19  tff(c_179, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))!=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_178])).
% 5.76/2.19  tff(c_22, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.76/2.19  tff(c_24, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.19  tff(c_53, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 5.76/2.19  tff(c_303, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(A_75, B_76, C_77), B_76) | r2_hidden('#skF_2'(A_75, B_76, C_77), C_77) | k3_xboole_0(A_75, B_76)=C_77)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.76/2.19  tff(c_26, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.76/2.19  tff(c_624, plain, (![A_117, B_118, C_119, A_120]: (r2_hidden('#skF_1'(A_117, B_118, C_119), A_120) | ~m1_subset_1(B_118, k1_zfmisc_1(A_120)) | r2_hidden('#skF_2'(A_117, B_118, C_119), C_119) | k3_xboole_0(A_117, B_118)=C_119)), inference(resolution, [status(thm)], [c_303, c_26])).
% 5.76/2.19  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.76/2.19  tff(c_668, plain, (![B_121, A_122, A_123]: (~m1_subset_1(B_121, k1_zfmisc_1(A_122)) | r2_hidden('#skF_2'(A_123, B_121, A_122), A_122) | k3_xboole_0(A_123, B_121)=A_122)), inference(resolution, [status(thm)], [c_624, c_16])).
% 5.76/2.19  tff(c_689, plain, (![A_123, B_121, A_122, A_11]: (r2_hidden('#skF_2'(A_123, B_121, A_122), A_11) | ~m1_subset_1(A_122, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_122)) | k3_xboole_0(A_123, B_121)=A_122)), inference(resolution, [status(thm)], [c_668, c_26])).
% 5.76/2.19  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_109, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_44])).
% 5.76/2.19  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.76/2.19  tff(c_330, plain, (![A_78, B_79, C_80]: (~r2_hidden('#skF_1'(A_78, B_79, C_80), C_80) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k3_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.76/2.19  tff(c_359, plain, (![A_84, B_85]: (r2_hidden('#skF_2'(A_84, B_85, B_85), B_85) | k3_xboole_0(A_84, B_85)=B_85)), inference(resolution, [status(thm)], [c_18, c_330])).
% 5.76/2.19  tff(c_387, plain, (![A_88, B_89, A_90]: (r2_hidden('#skF_2'(A_88, B_89, B_89), A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | k3_xboole_0(A_88, B_89)=B_89)), inference(resolution, [status(thm)], [c_359, c_26])).
% 5.76/2.19  tff(c_952, plain, (![A_153, B_154, A_155, A_156]: (r2_hidden('#skF_2'(A_153, B_154, B_154), A_155) | ~m1_subset_1(A_156, k1_zfmisc_1(A_155)) | ~m1_subset_1(B_154, k1_zfmisc_1(A_156)) | k3_xboole_0(A_153, B_154)=B_154)), inference(resolution, [status(thm)], [c_387, c_26])).
% 5.76/2.19  tff(c_960, plain, (![A_153, B_154]: (r2_hidden('#skF_2'(A_153, B_154, B_154), k2_struct_0('#skF_3')) | ~m1_subset_1(B_154, k1_zfmisc_1('#skF_5')) | k3_xboole_0(A_153, B_154)=B_154)), inference(resolution, [status(thm)], [c_109, c_952])).
% 5.76/2.19  tff(c_974, plain, (![A_159, B_160]: (r2_hidden('#skF_2'(A_159, B_160, B_160), k2_struct_0('#skF_3')) | ~m1_subset_1(B_160, k1_zfmisc_1('#skF_5')) | k3_xboole_0(A_159, B_160)=B_160)), inference(resolution, [status(thm)], [c_109, c_952])).
% 5.76/2.19  tff(c_12, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.76/2.19  tff(c_2311, plain, (![B_292]: (r2_hidden('#skF_1'(k2_struct_0('#skF_3'), B_292, B_292), B_292) | ~r2_hidden('#skF_2'(k2_struct_0('#skF_3'), B_292, B_292), B_292) | ~m1_subset_1(B_292, k1_zfmisc_1('#skF_5')) | k3_xboole_0(k2_struct_0('#skF_3'), B_292)=B_292)), inference(resolution, [status(thm)], [c_974, c_12])).
% 5.76/2.19  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.76/2.19  tff(c_2578, plain, (![B_311]: (~r2_hidden('#skF_2'(k2_struct_0('#skF_3'), B_311, B_311), k2_struct_0('#skF_3')) | ~r2_hidden('#skF_2'(k2_struct_0('#skF_3'), B_311, B_311), B_311) | ~m1_subset_1(B_311, k1_zfmisc_1('#skF_5')) | k3_xboole_0(k2_struct_0('#skF_3'), B_311)=B_311)), inference(resolution, [status(thm)], [c_2311, c_10])).
% 5.76/2.19  tff(c_2816, plain, (![B_322]: (~r2_hidden('#skF_2'(k2_struct_0('#skF_3'), B_322, B_322), B_322) | ~m1_subset_1(B_322, k1_zfmisc_1('#skF_5')) | k3_xboole_0(k2_struct_0('#skF_3'), B_322)=B_322)), inference(resolution, [status(thm)], [c_960, c_2578])).
% 5.76/2.19  tff(c_2840, plain, (![A_11]: (~m1_subset_1(A_11, k1_zfmisc_1('#skF_5')) | ~m1_subset_1(A_11, k1_zfmisc_1(A_11)) | k3_xboole_0(k2_struct_0('#skF_3'), A_11)=A_11)), inference(resolution, [status(thm)], [c_689, c_2816])).
% 5.76/2.19  tff(c_2933, plain, (![A_323]: (~m1_subset_1(A_323, k1_zfmisc_1('#skF_5')) | k3_xboole_0(k2_struct_0('#skF_3'), A_323)=A_323)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2840])).
% 5.76/2.19  tff(c_2938, plain, (k3_xboole_0(k2_struct_0('#skF_3'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_53, c_2933])).
% 5.76/2.19  tff(c_3143, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_3'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2938, c_2])).
% 5.76/2.19  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_157, plain, (![A_10, B_54]: (k9_subset_1(A_10, B_54, A_10)=k3_xboole_0(B_54, A_10))), inference(resolution, [status(thm)], [c_53, c_148])).
% 5.76/2.19  tff(c_46, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.76/2.19  tff(c_167, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=k2_struct_0(A_58) | ~v1_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.76/2.19  tff(c_170, plain, (![B_59]: (k2_pre_topc('#skF_3', B_59)=k2_struct_0('#skF_3') | ~v1_tops_1(B_59, '#skF_3') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_167])).
% 5.76/2.19  tff(c_198, plain, (![B_62]: (k2_pre_topc('#skF_3', B_62)=k2_struct_0('#skF_3') | ~v1_tops_1(B_62, '#skF_3') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_170])).
% 5.76/2.19  tff(c_201, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_198])).
% 5.76/2.19  tff(c_211, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_201])).
% 5.76/2.19  tff(c_576, plain, (![A_106, B_107, C_108]: (k2_pre_topc(A_106, k9_subset_1(u1_struct_0(A_106), B_107, k2_pre_topc(A_106, C_108)))=k2_pre_topc(A_106, k9_subset_1(u1_struct_0(A_106), B_107, C_108)) | ~v3_pre_topc(B_107, A_106) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.76/2.19  tff(c_591, plain, (![B_107]: (k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_107, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_107, '#skF_4')) | ~v3_pre_topc(B_107, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_576])).
% 5.76/2.19  tff(c_2480, plain, (![B_306]: (k2_pre_topc('#skF_3', k3_xboole_0(B_306, k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0(B_306, '#skF_4')) | ~v3_pre_topc(B_306, '#skF_3') | ~m1_subset_1(B_306, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_107, c_110, c_107, c_155, c_157, c_107, c_107, c_591])).
% 5.76/2.19  tff(c_2486, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', '#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_109, c_2480])).
% 5.76/2.19  tff(c_2495, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_5', k2_struct_0('#skF_3')))=k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2, c_2486])).
% 5.76/2.19  tff(c_3201, plain, (k2_pre_topc('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k2_pre_topc('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3143, c_2495])).
% 5.76/2.19  tff(c_3203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_3201])).
% 5.76/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.19  
% 5.76/2.19  Inference rules
% 5.76/2.19  ----------------------
% 5.76/2.19  #Ref     : 0
% 5.76/2.19  #Sup     : 758
% 5.76/2.19  #Fact    : 0
% 5.76/2.20  #Define  : 0
% 5.76/2.20  #Split   : 4
% 5.76/2.20  #Chain   : 0
% 5.76/2.20  #Close   : 0
% 5.76/2.20  
% 5.76/2.20  Ordering : KBO
% 5.76/2.20  
% 5.76/2.20  Simplification rules
% 5.76/2.20  ----------------------
% 5.76/2.20  #Subsume      : 233
% 5.76/2.20  #Demod        : 380
% 5.76/2.20  #Tautology    : 68
% 5.76/2.20  #SimpNegUnit  : 4
% 5.76/2.20  #BackRed      : 5
% 5.76/2.20  
% 5.76/2.20  #Partial instantiations: 0
% 5.76/2.20  #Strategies tried      : 1
% 5.76/2.20  
% 5.76/2.20  Timing (in seconds)
% 5.76/2.20  ----------------------
% 5.76/2.20  Preprocessing        : 0.36
% 5.76/2.20  Parsing              : 0.19
% 5.76/2.20  CNF conversion       : 0.03
% 5.76/2.20  Main loop            : 1.02
% 5.76/2.20  Inferencing          : 0.31
% 5.76/2.20  Reduction            : 0.34
% 5.76/2.20  Demodulation         : 0.26
% 5.76/2.20  BG Simplification    : 0.04
% 5.76/2.20  Subsumption          : 0.27
% 5.76/2.20  Abstraction          : 0.06
% 5.76/2.20  MUC search           : 0.00
% 5.76/2.20  Cooper               : 0.00
% 5.76/2.20  Total                : 1.42
% 5.76/2.20  Index Insertion      : 0.00
% 5.76/2.20  Index Deletion       : 0.00
% 5.76/2.20  Index Matching       : 0.00
% 5.76/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
