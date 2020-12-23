%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:19 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 321 expanded)
%              Number of leaves         :   40 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 920 expanded)
%              Number of equality atoms :   24 ( 135 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_135,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_40,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_66,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_28,plain,(
    ! [A_24] :
      ( v4_pre_topc(k2_struct_0(A_24),A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_26,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_26,c_113])).

tff(c_123,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_137,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_44])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_64,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_65,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_4') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63])).

tff(c_16,plain,(
    ! [C_13,A_7,B_11] :
      ( r2_hidden(C_13,k3_subset_1(A_7,B_11))
      | r2_hidden(C_13,B_11)
      | ~ m1_subset_1(C_13,A_7)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_473,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,k3_subset_1(A_87,B_88))
      | r2_hidden(C_86,B_88)
      | ~ m1_subset_1(C_86,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87))
      | A_87 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_482,plain,(
    ! [C_86,A_5] :
      ( r2_hidden(C_86,A_5)
      | r2_hidden(C_86,'#skF_4')
      | ~ m1_subset_1(C_86,A_5)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_5))
      | A_5 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_473])).

tff(c_503,plain,(
    ! [C_89,A_90] :
      ( r2_hidden(C_89,A_90)
      | r2_hidden(C_89,'#skF_4')
      | ~ m1_subset_1(C_89,A_90)
      | A_90 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_482])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_538,plain,(
    ! [C_89,A_90] :
      ( ~ r1_tarski('#skF_4',C_89)
      | r2_hidden(C_89,A_90)
      | ~ m1_subset_1(C_89,A_90)
      | A_90 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_503,c_22])).

tff(c_550,plain,(
    ! [C_89,A_90] :
      ( r2_hidden(C_89,A_90)
      | ~ m1_subset_1(C_89,A_90)
      | A_90 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_538])).

tff(c_30,plain,(
    ! [A_25] :
      ( v3_pre_topc(k2_struct_0(A_25),A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,(
    ! [A_47] : m1_subset_1(A_47,k1_zfmisc_1(A_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_56,plain,(
    ! [D_39] :
      ( v4_pre_topc(D_39,'#skF_2')
      | ~ r2_hidden(D_39,'#skF_4')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_111,plain,
    ( v4_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_56])).

tff(c_155,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_123,c_111])).

tff(c_156,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_62,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_52,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_4')
      | ~ r2_hidden('#skF_3',D_39)
      | ~ v4_pre_topc(D_39,'#skF_2')
      | ~ v3_pre_topc(D_39,'#skF_2')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_208,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_4')
      | ~ r2_hidden('#skF_3',D_69)
      | ~ v4_pre_topc(D_69,'#skF_2')
      | ~ v3_pre_topc(D_69,'#skF_2')
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_52])).

tff(c_215,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_208])).

tff(c_223,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_215])).

tff(c_705,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_708,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_705])).

tff(c_712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_708])).

tff(c_713,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_721,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_724,plain,
    ( ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_550,c_721])).

tff(c_727,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_724])).

tff(c_181,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_1'(A_68),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_189,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_181])).

tff(c_193,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_189])).

tff(c_194,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_193])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_205,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_206,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_736,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_206])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_736])).

tff(c_746,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_759,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_746])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_759])).

tff(c_764,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_36,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0('#skF_1'(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_768,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_764,c_36])).

tff(c_771,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_768])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_771])).

tff(c_775,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_779,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_775,c_22])).

tff(c_783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:29:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.92/1.45  
% 2.92/1.45  %Foreground sorts:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Background operators:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Foreground operators:
% 2.92/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.92/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.92/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.45  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.92/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.92/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.92/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.92/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.45  
% 3.08/1.46  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.08/1.46  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.08/1.46  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.08/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.08/1.46  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.08/1.46  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.08/1.46  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.08/1.46  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.08/1.46  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.08/1.46  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.08/1.46  tff(f_52, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.08/1.46  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.08/1.46  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.08/1.46  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.08/1.46  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.08/1.46  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.08/1.46  tff(c_40, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.08/1.46  tff(c_66, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 3.08/1.46  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_28, plain, (![A_24]: (v4_pre_topc(k2_struct_0(A_24), A_24) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.08/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.08/1.46  tff(c_67, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2])).
% 3.08/1.46  tff(c_26, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.08/1.46  tff(c_113, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.08/1.46  tff(c_119, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_26, c_113])).
% 3.08/1.46  tff(c_123, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_119])).
% 3.08/1.46  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_137, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_44])).
% 3.08/1.46  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.46  tff(c_60, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14])).
% 3.08/1.46  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.08/1.46  tff(c_64, plain, (![A_2]: (k1_subset_1(A_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6])).
% 3.08/1.46  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.46  tff(c_12, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.46  tff(c_63, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 3.08/1.46  tff(c_65, plain, (![A_5]: (k3_subset_1(A_5, '#skF_4')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63])).
% 3.08/1.46  tff(c_16, plain, (![C_13, A_7, B_11]: (r2_hidden(C_13, k3_subset_1(A_7, B_11)) | r2_hidden(C_13, B_11) | ~m1_subset_1(C_13, A_7) | ~m1_subset_1(B_11, k1_zfmisc_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.46  tff(c_473, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, k3_subset_1(A_87, B_88)) | r2_hidden(C_86, B_88) | ~m1_subset_1(C_86, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)) | A_87='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 3.08/1.46  tff(c_482, plain, (![C_86, A_5]: (r2_hidden(C_86, A_5) | r2_hidden(C_86, '#skF_4') | ~m1_subset_1(C_86, A_5) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_5)) | A_5='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_65, c_473])).
% 3.08/1.46  tff(c_503, plain, (![C_89, A_90]: (r2_hidden(C_89, A_90) | r2_hidden(C_89, '#skF_4') | ~m1_subset_1(C_89, A_90) | A_90='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_482])).
% 3.08/1.46  tff(c_22, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.08/1.46  tff(c_538, plain, (![C_89, A_90]: (~r1_tarski('#skF_4', C_89) | r2_hidden(C_89, A_90) | ~m1_subset_1(C_89, A_90) | A_90='#skF_4')), inference(resolution, [status(thm)], [c_503, c_22])).
% 3.08/1.46  tff(c_550, plain, (![C_89, A_90]: (r2_hidden(C_89, A_90) | ~m1_subset_1(C_89, A_90) | A_90='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_538])).
% 3.08/1.46  tff(c_30, plain, (![A_25]: (v3_pre_topc(k2_struct_0(A_25), A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.46  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.46  tff(c_106, plain, (![A_47]: (m1_subset_1(A_47, k1_zfmisc_1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.08/1.46  tff(c_56, plain, (![D_39]: (v4_pre_topc(D_39, '#skF_2') | ~r2_hidden(D_39, '#skF_4') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_111, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_106, c_56])).
% 3.08/1.46  tff(c_155, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_123, c_111])).
% 3.08/1.46  tff(c_156, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_155])).
% 3.08/1.46  tff(c_62, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.08/1.46  tff(c_52, plain, (![D_39]: (r2_hidden(D_39, '#skF_4') | ~r2_hidden('#skF_3', D_39) | ~v4_pre_topc(D_39, '#skF_2') | ~v3_pre_topc(D_39, '#skF_2') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.08/1.46  tff(c_208, plain, (![D_69]: (r2_hidden(D_69, '#skF_4') | ~r2_hidden('#skF_3', D_69) | ~v4_pre_topc(D_69, '#skF_2') | ~v3_pre_topc(D_69, '#skF_2') | ~m1_subset_1(D_69, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_52])).
% 3.08/1.46  tff(c_215, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_62, c_208])).
% 3.08/1.46  tff(c_223, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_156, c_215])).
% 3.08/1.46  tff(c_705, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_223])).
% 3.08/1.46  tff(c_708, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_705])).
% 3.08/1.46  tff(c_712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_708])).
% 3.08/1.46  tff(c_713, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_223])).
% 3.08/1.46  tff(c_721, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_713])).
% 3.08/1.46  tff(c_724, plain, (~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_550, c_721])).
% 3.08/1.46  tff(c_727, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_724])).
% 3.08/1.46  tff(c_181, plain, (![A_68]: (m1_subset_1('#skF_1'(A_68), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.08/1.46  tff(c_189, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_181])).
% 3.08/1.46  tff(c_193, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_189])).
% 3.08/1.46  tff(c_194, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_193])).
% 3.08/1.46  tff(c_18, plain, (![B_16, A_14]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.46  tff(c_205, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_194, c_18])).
% 3.08/1.46  tff(c_206, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_205])).
% 3.08/1.46  tff(c_736, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_727, c_206])).
% 3.08/1.46  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_736])).
% 3.08/1.46  tff(c_746, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_713])).
% 3.08/1.46  tff(c_759, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_746])).
% 3.08/1.46  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_759])).
% 3.08/1.46  tff(c_764, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_205])).
% 3.08/1.46  tff(c_36, plain, (![A_26]: (~v1_xboole_0('#skF_1'(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.08/1.46  tff(c_768, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_764, c_36])).
% 3.08/1.46  tff(c_771, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_768])).
% 3.08/1.46  tff(c_773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_771])).
% 3.08/1.46  tff(c_775, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_155])).
% 3.08/1.46  tff(c_779, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_775, c_22])).
% 3.08/1.46  tff(c_783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_779])).
% 3.08/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  Inference rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Ref     : 0
% 3.08/1.46  #Sup     : 117
% 3.08/1.46  #Fact    : 4
% 3.08/1.46  #Define  : 0
% 3.08/1.46  #Split   : 18
% 3.08/1.46  #Chain   : 0
% 3.08/1.46  #Close   : 0
% 3.08/1.46  
% 3.08/1.46  Ordering : KBO
% 3.08/1.46  
% 3.08/1.46  Simplification rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Subsume      : 42
% 3.08/1.46  #Demod        : 107
% 3.08/1.46  #Tautology    : 43
% 3.08/1.46  #SimpNegUnit  : 20
% 3.08/1.46  #BackRed      : 38
% 3.08/1.46  
% 3.08/1.46  #Partial instantiations: 0
% 3.08/1.46  #Strategies tried      : 1
% 3.08/1.46  
% 3.08/1.46  Timing (in seconds)
% 3.08/1.47  ----------------------
% 3.08/1.47  Preprocessing        : 0.33
% 3.08/1.47  Parsing              : 0.18
% 3.08/1.47  CNF conversion       : 0.02
% 3.08/1.47  Main loop            : 0.33
% 3.08/1.47  Inferencing          : 0.11
% 3.08/1.47  Reduction            : 0.11
% 3.08/1.47  Demodulation         : 0.07
% 3.08/1.47  BG Simplification    : 0.02
% 3.08/1.47  Subsumption          : 0.06
% 3.08/1.47  Abstraction          : 0.01
% 3.08/1.47  MUC search           : 0.00
% 3.08/1.47  Cooper               : 0.00
% 3.08/1.47  Total                : 0.71
% 3.08/1.47  Index Insertion      : 0.00
% 3.08/1.47  Index Deletion       : 0.00
% 3.08/1.47  Index Matching       : 0.00
% 3.08/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
