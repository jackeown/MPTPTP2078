%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:20 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 334 expanded)
%              Number of leaves         :   45 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 902 expanded)
%              Number of equality atoms :   22 ( 140 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    ! [A_26] :
      ( v4_pre_topc(k2_struct_0(A_26),A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_113,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_123,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_119])).

tff(c_151,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(u1_struct_0(A_57))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_154,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_151])).

tff(c_155,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_154])).

tff(c_156,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_160,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_156])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_160])).

tff(c_165,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_137,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_46])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [A_47] : m1_subset_1(A_47,k1_zfmisc_1(A_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_58,plain,(
    ! [D_41] :
      ( v4_pre_topc(D_41,'#skF_1')
      | ~ r2_hidden(D_41,'#skF_3')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_98,plain,
    ( v4_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_58])).

tff(c_217,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_123,c_98])).

tff(c_218,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_63,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_54,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_3')
      | ~ r2_hidden('#skF_2',D_41)
      | ~ v4_pre_topc(D_41,'#skF_1')
      | ~ v3_pre_topc(D_41,'#skF_1')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_243,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,'#skF_3')
      | ~ r2_hidden('#skF_2',D_73)
      | ~ v4_pre_topc(D_73,'#skF_1')
      | ~ v3_pre_topc(D_73,'#skF_1')
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_54])).

tff(c_251,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_243])).

tff(c_257,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_251])).

tff(c_327,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    ! [A_10] : m1_subset_1('#skF_3',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_328,plain,(
    ! [B_82,A_83] :
      ( v4_pre_topc(B_82,A_83)
      | ~ v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_331,plain,(
    ! [B_82] :
      ( v4_pre_topc(B_82,'#skF_1')
      | ~ v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_328])).

tff(c_347,plain,(
    ! [B_85] :
      ( v4_pre_topc(B_85,'#skF_1')
      | ~ v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_331])).

tff(c_351,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_347])).

tff(c_358,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_351])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_6])).

tff(c_195,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_204,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_3') = k4_xboole_0(A_3,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_195])).

tff(c_207,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_3') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_204])).

tff(c_266,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_269,plain,(
    ! [A_10] : k4_xboole_0(A_10,'#skF_3') = k3_subset_1(A_10,'#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_266])).

tff(c_274,plain,(
    ! [A_10] : k3_subset_1(A_10,'#skF_3') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_269])).

tff(c_360,plain,(
    ! [A_86,B_87] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_86),B_87),A_86)
      | ~ v4_pre_topc(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_364,plain,(
    ! [A_86] :
      ( v3_pre_topc(u1_struct_0(A_86),A_86)
      | ~ v4_pre_topc('#skF_3',A_86)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_360])).

tff(c_372,plain,(
    ! [A_88] :
      ( v3_pre_topc(u1_struct_0(A_88),A_88)
      | ~ v4_pre_topc('#skF_3',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_364])).

tff(c_375,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_372])).

tff(c_377,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_358,c_375])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_377])).

tff(c_380,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_385,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_382])).

tff(c_388,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_385])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_388])).

tff(c_391,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_404,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_391])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_404])).

tff(c_410,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_413,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_410,c_26])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.39  
% 2.61/1.39  %Foreground sorts:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Background operators:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Foreground operators:
% 2.61/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.61/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.61/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.61/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.39  
% 2.61/1.41  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.61/1.41  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.61/1.41  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.61/1.41  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.61/1.41  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.61/1.41  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.61/1.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.61/1.41  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.61/1.41  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.61/1.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.61/1.41  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.61/1.41  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.61/1.41  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.61/1.41  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.61/1.41  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.41  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.61/1.41  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.61/1.41  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.61/1.41  tff(c_42, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.41  tff(c_65, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 2.61/1.41  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_36, plain, (![A_26]: (v4_pre_topc(k2_struct_0(A_26), A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.41  tff(c_32, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.61/1.41  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_113, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.41  tff(c_119, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.61/1.41  tff(c_123, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_119])).
% 2.61/1.41  tff(c_151, plain, (![A_57]: (~v1_xboole_0(u1_struct_0(A_57)) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.61/1.41  tff(c_154, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_123, c_151])).
% 2.61/1.41  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_154])).
% 2.61/1.41  tff(c_156, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_155])).
% 2.61/1.41  tff(c_160, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_156])).
% 2.61/1.41  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_160])).
% 2.61/1.41  tff(c_165, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_155])).
% 2.61/1.41  tff(c_46, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_137, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_46])).
% 2.61/1.41  tff(c_22, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.61/1.41  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.41  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.41  tff(c_93, plain, (![A_47]: (m1_subset_1(A_47, k1_zfmisc_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.61/1.41  tff(c_58, plain, (![D_41]: (v4_pre_topc(D_41, '#skF_1') | ~r2_hidden(D_41, '#skF_3') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_98, plain, (v4_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(u1_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_58])).
% 2.61/1.41  tff(c_217, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_123, c_98])).
% 2.61/1.41  tff(c_218, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_217])).
% 2.61/1.41  tff(c_63, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.61/1.41  tff(c_54, plain, (![D_41]: (r2_hidden(D_41, '#skF_3') | ~r2_hidden('#skF_2', D_41) | ~v4_pre_topc(D_41, '#skF_1') | ~v3_pre_topc(D_41, '#skF_1') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.61/1.41  tff(c_243, plain, (![D_73]: (r2_hidden(D_73, '#skF_3') | ~r2_hidden('#skF_2', D_73) | ~v4_pre_topc(D_73, '#skF_1') | ~v3_pre_topc(D_73, '#skF_1') | ~m1_subset_1(D_73, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_54])).
% 2.61/1.41  tff(c_251, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_63, c_243])).
% 2.61/1.41  tff(c_257, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_218, c_251])).
% 2.61/1.41  tff(c_327, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_257])).
% 2.61/1.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.61/1.41  tff(c_67, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.61/1.41  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.41  tff(c_61, plain, (![A_10]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 2.61/1.41  tff(c_328, plain, (![B_82, A_83]: (v4_pre_topc(B_82, A_83) | ~v1_xboole_0(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.41  tff(c_331, plain, (![B_82]: (v4_pre_topc(B_82, '#skF_1') | ~v1_xboole_0(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_328])).
% 2.61/1.41  tff(c_347, plain, (![B_85]: (v4_pre_topc(B_85, '#skF_1') | ~v1_xboole_0(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_331])).
% 2.61/1.41  tff(c_351, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_61, c_347])).
% 2.61/1.41  tff(c_358, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_351])).
% 2.61/1.41  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.41  tff(c_64, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 2.61/1.41  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.61/1.41  tff(c_66, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_6])).
% 2.61/1.41  tff(c_195, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.61/1.41  tff(c_204, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_3')=k4_xboole_0(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_195])).
% 2.61/1.41  tff(c_207, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_3')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_204])).
% 2.61/1.41  tff(c_266, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.61/1.41  tff(c_269, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_3')=k3_subset_1(A_10, '#skF_3'))), inference(resolution, [status(thm)], [c_61, c_266])).
% 2.61/1.41  tff(c_274, plain, (![A_10]: (k3_subset_1(A_10, '#skF_3')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_207, c_269])).
% 2.61/1.41  tff(c_360, plain, (![A_86, B_87]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_86), B_87), A_86) | ~v4_pre_topc(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.61/1.41  tff(c_364, plain, (![A_86]: (v3_pre_topc(u1_struct_0(A_86), A_86) | ~v4_pre_topc('#skF_3', A_86) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(superposition, [status(thm), theory('equality')], [c_274, c_360])).
% 2.61/1.41  tff(c_372, plain, (![A_88]: (v3_pre_topc(u1_struct_0(A_88), A_88) | ~v4_pre_topc('#skF_3', A_88) | ~l1_pre_topc(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_364])).
% 2.61/1.41  tff(c_375, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_123, c_372])).
% 2.61/1.41  tff(c_377, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_358, c_375])).
% 2.61/1.41  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_377])).
% 2.61/1.41  tff(c_380, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_257])).
% 2.61/1.41  tff(c_382, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_380])).
% 2.61/1.41  tff(c_385, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_382])).
% 2.61/1.41  tff(c_388, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_385])).
% 2.61/1.41  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_388])).
% 2.61/1.41  tff(c_391, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_380])).
% 2.61/1.41  tff(c_404, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_391])).
% 2.61/1.41  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_404])).
% 2.61/1.41  tff(c_410, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_217])).
% 2.61/1.41  tff(c_26, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.41  tff(c_413, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_410, c_26])).
% 2.61/1.41  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_413])).
% 2.61/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  Inference rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Ref     : 0
% 2.61/1.41  #Sup     : 63
% 2.61/1.41  #Fact    : 0
% 2.61/1.41  #Define  : 0
% 2.61/1.41  #Split   : 6
% 2.61/1.41  #Chain   : 0
% 2.61/1.41  #Close   : 0
% 2.61/1.41  
% 2.61/1.41  Ordering : KBO
% 2.61/1.41  
% 2.61/1.41  Simplification rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Subsume      : 9
% 2.61/1.41  #Demod        : 41
% 2.61/1.41  #Tautology    : 30
% 2.61/1.41  #SimpNegUnit  : 6
% 2.61/1.41  #BackRed      : 3
% 2.61/1.41  
% 2.61/1.41  #Partial instantiations: 0
% 2.61/1.41  #Strategies tried      : 1
% 2.61/1.41  
% 2.61/1.41  Timing (in seconds)
% 2.61/1.41  ----------------------
% 2.61/1.41  Preprocessing        : 0.34
% 2.61/1.41  Parsing              : 0.19
% 2.61/1.41  CNF conversion       : 0.02
% 2.61/1.41  Main loop            : 0.25
% 2.61/1.41  Inferencing          : 0.09
% 2.61/1.41  Reduction            : 0.08
% 2.61/1.41  Demodulation         : 0.06
% 2.61/1.41  BG Simplification    : 0.02
% 2.61/1.41  Subsumption          : 0.04
% 2.61/1.41  Abstraction          : 0.01
% 2.61/1.41  MUC search           : 0.00
% 2.61/1.41  Cooper               : 0.00
% 2.61/1.41  Total                : 0.63
% 2.61/1.41  Index Insertion      : 0.00
% 2.61/1.41  Index Deletion       : 0.00
% 2.61/1.41  Index Matching       : 0.00
% 2.61/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
