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
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 338 expanded)
%              Number of leaves         :   41 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 ( 965 expanded)
%              Number of equality atoms :   15 ( 135 expanded)
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

tff(f_139,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_30,plain,(
    ! [A_22] :
      ( v4_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_114,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_124,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_210,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_1'(A_70),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_218,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_210])).

tff(c_222,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_218])).

tff(c_223,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_222])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_234,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_223,c_16])).

tff(c_235,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_138,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_46])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [A_45] : m1_subset_1(A_45,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_58,plain,(
    ! [D_39] :
      ( v4_pre_topc(D_39,'#skF_2')
      | ~ r2_hidden(D_39,'#skF_4')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_97,plain,
    ( v4_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_58])).

tff(c_165,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_124,c_97])).

tff(c_166,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_63,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_54,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_4')
      | ~ r2_hidden('#skF_3',D_39)
      | ~ v4_pre_topc(D_39,'#skF_2')
      | ~ v3_pre_topc(D_39,'#skF_2')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_237,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,'#skF_4')
      | ~ r2_hidden('#skF_3',D_71)
      | ~ v4_pre_topc(D_71,'#skF_2')
      | ~ v3_pre_topc(D_71,'#skF_2')
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_54])).

tff(c_248,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_237])).

tff(c_255,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_248])).

tff(c_374,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_269,plain,(
    ! [B_73,A_74] :
      ( v4_pre_topc(B_73,A_74)
      | ~ v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_275,plain,(
    ! [B_73] :
      ( v4_pre_topc(B_73,'#skF_2')
      | ~ v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_269])).

tff(c_292,plain,(
    ! [B_76] :
      ( v4_pre_topc(B_76,'#skF_2')
      | ~ v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_275])).

tff(c_299,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_292])).

tff(c_307,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_299])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_65,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_12,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_66,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_4') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64])).

tff(c_390,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_88),B_89),A_88)
      | ~ v4_pre_topc(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_400,plain,(
    ! [A_88] :
      ( v3_pre_topc(u1_struct_0(A_88),A_88)
      | ~ v4_pre_topc('#skF_4',A_88)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_390])).

tff(c_406,plain,(
    ! [A_90] :
      ( v3_pre_topc(u1_struct_0(A_90),A_90)
      | ~ v4_pre_topc('#skF_4',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_400])).

tff(c_412,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_406])).

tff(c_415,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_307,c_412])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_415])).

tff(c_418,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_420,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_423,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_420])).

tff(c_426,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_423])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_426])).

tff(c_429,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_444,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_429])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_444])).

tff(c_449,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_34,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0('#skF_1'(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_453,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_449,c_34])).

tff(c_456,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_453])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_456])).

tff(c_460,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_463,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_460,c_22])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_463])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.34  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.44/1.34  
% 2.44/1.34  %Foreground sorts:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Background operators:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Foreground operators:
% 2.44/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.44/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.44/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.44/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.44/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.34  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.44/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.44/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.44/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.44/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.34  
% 2.82/1.36  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.82/1.36  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.82/1.36  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.82/1.36  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.82/1.36  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.82/1.36  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.82/1.36  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.82/1.36  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.82/1.36  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.82/1.36  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.82/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.82/1.36  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.82/1.36  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.82/1.36  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.82/1.36  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.82/1.36  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.82/1.36  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.82/1.36  tff(c_42, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.82/1.36  tff(c_67, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 2.82/1.36  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_30, plain, (![A_22]: (v4_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.82/1.36  tff(c_28, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.82/1.36  tff(c_114, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.82/1.36  tff(c_120, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.82/1.36  tff(c_124, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_120])).
% 2.82/1.36  tff(c_210, plain, (![A_70]: (m1_subset_1('#skF_1'(A_70), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.36  tff(c_218, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_210])).
% 2.82/1.36  tff(c_222, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_218])).
% 2.82/1.36  tff(c_223, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_222])).
% 2.82/1.36  tff(c_16, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.36  tff(c_234, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_223, c_16])).
% 2.82/1.36  tff(c_235, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_234])).
% 2.82/1.36  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_138, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_46])).
% 2.82/1.36  tff(c_18, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.36  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.36  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.82/1.36  tff(c_92, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.82/1.36  tff(c_58, plain, (![D_39]: (v4_pre_topc(D_39, '#skF_2') | ~r2_hidden(D_39, '#skF_4') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_97, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_92, c_58])).
% 2.82/1.36  tff(c_165, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_124, c_97])).
% 2.82/1.36  tff(c_166, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_165])).
% 2.82/1.36  tff(c_63, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.82/1.36  tff(c_54, plain, (![D_39]: (r2_hidden(D_39, '#skF_4') | ~r2_hidden('#skF_3', D_39) | ~v4_pre_topc(D_39, '#skF_2') | ~v3_pre_topc(D_39, '#skF_2') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.36  tff(c_237, plain, (![D_71]: (r2_hidden(D_71, '#skF_4') | ~r2_hidden('#skF_3', D_71) | ~v4_pre_topc(D_71, '#skF_2') | ~v3_pre_topc(D_71, '#skF_2') | ~m1_subset_1(D_71, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_54])).
% 2.82/1.36  tff(c_248, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_63, c_237])).
% 2.82/1.36  tff(c_255, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_166, c_248])).
% 2.82/1.36  tff(c_374, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_255])).
% 2.82/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.82/1.36  tff(c_68, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.82/1.36  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.36  tff(c_61, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 2.82/1.36  tff(c_269, plain, (![B_73, A_74]: (v4_pre_topc(B_73, A_74) | ~v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.82/1.36  tff(c_275, plain, (![B_73]: (v4_pre_topc(B_73, '#skF_2') | ~v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_269])).
% 2.82/1.36  tff(c_292, plain, (![B_76]: (v4_pre_topc(B_76, '#skF_2') | ~v1_xboole_0(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_275])).
% 2.82/1.36  tff(c_299, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_61, c_292])).
% 2.82/1.36  tff(c_307, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_299])).
% 2.82/1.36  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.82/1.36  tff(c_65, plain, (![A_2]: (k1_subset_1(A_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 2.82/1.36  tff(c_12, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.82/1.36  tff(c_64, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.82/1.36  tff(c_66, plain, (![A_5]: (k3_subset_1(A_5, '#skF_4')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64])).
% 2.82/1.36  tff(c_390, plain, (![A_88, B_89]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_88), B_89), A_88) | ~v4_pre_topc(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.82/1.36  tff(c_400, plain, (![A_88]: (v3_pre_topc(u1_struct_0(A_88), A_88) | ~v4_pre_topc('#skF_4', A_88) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(superposition, [status(thm), theory('equality')], [c_66, c_390])).
% 2.82/1.36  tff(c_406, plain, (![A_90]: (v3_pre_topc(u1_struct_0(A_90), A_90) | ~v4_pre_topc('#skF_4', A_90) | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_400])).
% 2.82/1.36  tff(c_412, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_406])).
% 2.82/1.36  tff(c_415, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_307, c_412])).
% 2.82/1.36  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_415])).
% 2.82/1.36  tff(c_418, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_255])).
% 2.82/1.36  tff(c_420, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_418])).
% 2.82/1.36  tff(c_423, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_420])).
% 2.82/1.36  tff(c_426, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_423])).
% 2.82/1.36  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_426])).
% 2.82/1.36  tff(c_429, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_418])).
% 2.82/1.36  tff(c_444, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_429])).
% 2.82/1.36  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_444])).
% 2.82/1.36  tff(c_449, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_234])).
% 2.82/1.36  tff(c_34, plain, (![A_23]: (~v1_xboole_0('#skF_1'(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.36  tff(c_453, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_449, c_34])).
% 2.82/1.36  tff(c_456, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_453])).
% 2.82/1.36  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_456])).
% 2.82/1.36  tff(c_460, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_165])).
% 2.82/1.36  tff(c_22, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.82/1.36  tff(c_463, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_460, c_22])).
% 2.82/1.36  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_463])).
% 2.82/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.36  
% 2.82/1.36  Inference rules
% 2.82/1.36  ----------------------
% 2.82/1.36  #Ref     : 0
% 2.82/1.36  #Sup     : 70
% 2.82/1.36  #Fact    : 0
% 2.82/1.36  #Define  : 0
% 2.82/1.36  #Split   : 10
% 2.82/1.36  #Chain   : 0
% 2.82/1.36  #Close   : 0
% 2.82/1.36  
% 2.82/1.36  Ordering : KBO
% 2.82/1.36  
% 2.82/1.36  Simplification rules
% 2.82/1.36  ----------------------
% 2.82/1.36  #Subsume      : 15
% 2.82/1.36  #Demod        : 54
% 2.82/1.36  #Tautology    : 23
% 2.82/1.36  #SimpNegUnit  : 10
% 2.82/1.36  #BackRed      : 3
% 2.82/1.36  
% 2.82/1.36  #Partial instantiations: 0
% 2.82/1.36  #Strategies tried      : 1
% 2.82/1.36  
% 2.82/1.36  Timing (in seconds)
% 2.82/1.36  ----------------------
% 2.82/1.37  Preprocessing        : 0.32
% 2.82/1.37  Parsing              : 0.17
% 2.82/1.37  CNF conversion       : 0.02
% 2.82/1.37  Main loop            : 0.26
% 2.82/1.37  Inferencing          : 0.09
% 2.82/1.37  Reduction            : 0.08
% 2.82/1.37  Demodulation         : 0.06
% 2.82/1.37  BG Simplification    : 0.02
% 2.82/1.37  Subsumption          : 0.04
% 2.82/1.37  Abstraction          : 0.01
% 2.82/1.37  MUC search           : 0.00
% 2.82/1.37  Cooper               : 0.00
% 2.82/1.37  Total                : 0.62
% 2.82/1.37  Index Insertion      : 0.00
% 2.82/1.37  Index Deletion       : 0.00
% 2.82/1.37  Index Matching       : 0.00
% 2.82/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
