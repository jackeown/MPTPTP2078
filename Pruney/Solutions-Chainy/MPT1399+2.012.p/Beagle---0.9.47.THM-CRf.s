%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:20 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 404 expanded)
%              Number of leaves         :   42 ( 151 expanded)
%              Depth                    :   13
%              Number of atoms          :  211 (1114 expanded)
%              Number of equality atoms :   19 ( 177 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

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

tff(f_140,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tops_1)).

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

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_34,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_202,plain,(
    ! [B_68,A_69] :
      ( v2_tops_1(B_68,A_69)
      | ~ v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_209,plain,(
    ! [A_69] :
      ( v2_tops_1('#skF_3',A_69)
      | ~ v1_xboole_0('#skF_3')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_59,c_202])).

tff(c_218,plain,(
    ! [A_69] :
      ( v2_tops_1('#skF_3',A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_209])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_113,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_117,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_113])).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_240,plain,(
    ! [A_74] :
      ( v2_tops_1(u1_struct_0(A_74),A_74)
      | ~ v1_xboole_0(u1_struct_0(A_74))
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_61,c_202])).

tff(c_243,plain,
    ( v2_tops_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_240])).

tff(c_245,plain,
    ( v2_tops_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_117,c_243])).

tff(c_246,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_118,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_44])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [A_20] :
      ( v4_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_3] : k1_subset_1(A_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8])).

tff(c_14,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_subset_1(A_6)) = k2_subset_1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_subset_1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_64,plain,(
    ! [A_6] : k3_subset_1(A_6,'#skF_3') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62])).

tff(c_277,plain,(
    ! [B_77,A_78] :
      ( v4_pre_topc(B_77,A_78)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_78),B_77),A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_284,plain,(
    ! [A_78] :
      ( v4_pre_topc('#skF_3',A_78)
      | ~ v3_pre_topc(u1_struct_0(A_78),A_78)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_277])).

tff(c_289,plain,(
    ! [A_79] :
      ( v4_pre_topc('#skF_3',A_79)
      | ~ v3_pre_topc(u1_struct_0(A_79),A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_284])).

tff(c_292,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_289])).

tff(c_294,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_292])).

tff(c_295,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_221,plain,(
    ! [B_71,A_72] :
      ( v4_pre_topc(B_71,A_72)
      | ~ v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,(
    ! [B_71] :
      ( v4_pre_topc(B_71,'#skF_1')
      | ~ v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_221])).

tff(c_296,plain,(
    ! [B_80] :
      ( v4_pre_topc(B_80,'#skF_1')
      | ~ v1_xboole_0(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_224])).

tff(c_300,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_296])).

tff(c_307,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_300])).

tff(c_322,plain,(
    ! [A_83,B_84] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_83),B_84),A_83)
      | ~ v4_pre_topc(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_332,plain,(
    ! [A_83] :
      ( v3_pre_topc(u1_struct_0(A_83),A_83)
      | ~ v4_pre_topc('#skF_3',A_83)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_322])).

tff(c_338,plain,(
    ! [A_85] :
      ( v3_pre_topc(u1_struct_0(A_85),A_85)
      | ~ v4_pre_topc('#skF_3',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_332])).

tff(c_344,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_338])).

tff(c_347,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_307,c_344])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_347])).

tff(c_351,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_58,plain,(
    ! [D_39] :
      ( v3_pre_topc(D_39,'#skF_1')
      | ~ r2_hidden(D_39,'#skF_3')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_124,plain,(
    ! [D_52] :
      ( v3_pre_topc(D_52,'#skF_1')
      | ~ r2_hidden(D_52,'#skF_3')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_58])).

tff(c_134,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_124])).

tff(c_154,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_52,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_3')
      | ~ r2_hidden('#skF_2',D_39)
      | ~ v4_pre_topc(D_39,'#skF_1')
      | ~ v3_pre_topc(D_39,'#skF_1')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_248,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,'#skF_3')
      | ~ r2_hidden('#skF_2',D_75)
      | ~ v4_pre_topc(D_75,'#skF_1')
      | ~ v3_pre_topc(D_75,'#skF_1')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_52])).

tff(c_256,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_248])).

tff(c_262,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_256])).

tff(c_366,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_262])).

tff(c_367,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_370,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_367])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_370])).

tff(c_375,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_379,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_375])).

tff(c_382,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_379])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_382])).

tff(c_386,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_390,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_386,c_66])).

tff(c_38,plain,(
    ! [A_27] :
      ( ~ v2_tops_1(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_402,plain,
    ( ~ v2_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_38])).

tff(c_409,plain,
    ( ~ v2_tops_1('#skF_3','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_402])).

tff(c_410,plain,(
    ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_409])).

tff(c_465,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_218,c_410])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_465])).

tff(c_471,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_474,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_471,c_22])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:32:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.32  
% 2.60/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.33  %$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.33  
% 2.60/1.33  %Foreground sorts:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Background operators:
% 2.60/1.33  
% 2.60/1.33  
% 2.60/1.33  %Foreground operators:
% 2.60/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.33  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.33  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.60/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.60/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.60/1.33  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.60/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.60/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.60/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.60/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.33  
% 2.60/1.35  tff(f_140, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.60/1.35  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.60/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.60/1.35  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.60/1.35  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tops_1)).
% 2.60/1.35  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.60/1.35  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.60/1.35  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.60/1.35  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.60/1.35  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.60/1.35  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.60/1.35  tff(f_34, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.60/1.35  tff(f_40, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.60/1.35  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.60/1.35  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.60/1.35  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.60/1.35  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ~v2_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_tops_1)).
% 2.60/1.35  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.60/1.35  tff(c_40, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.35  tff(c_65, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6])).
% 2.60/1.35  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.60/1.35  tff(c_67, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2])).
% 2.60/1.35  tff(c_16, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.60/1.35  tff(c_59, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 2.60/1.35  tff(c_202, plain, (![B_68, A_69]: (v2_tops_1(B_68, A_69) | ~v1_xboole_0(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.60/1.35  tff(c_209, plain, (![A_69]: (v2_tops_1('#skF_3', A_69) | ~v1_xboole_0('#skF_3') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_59, c_202])).
% 2.60/1.35  tff(c_218, plain, (![A_69]: (v2_tops_1('#skF_3', A_69) | ~l1_pre_topc(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_209])).
% 2.60/1.35  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_28, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.60/1.35  tff(c_107, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.35  tff(c_113, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_28, c_107])).
% 2.60/1.35  tff(c_117, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_113])).
% 2.60/1.35  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.60/1.35  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.60/1.35  tff(c_61, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.60/1.35  tff(c_240, plain, (![A_74]: (v2_tops_1(u1_struct_0(A_74), A_74) | ~v1_xboole_0(u1_struct_0(A_74)) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_61, c_202])).
% 2.60/1.35  tff(c_243, plain, (v2_tops_1(k2_struct_0('#skF_1'), '#skF_1') | ~v1_xboole_0(u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_240])).
% 2.60/1.35  tff(c_245, plain, (v2_tops_1(k2_struct_0('#skF_1'), '#skF_1') | ~v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_117, c_243])).
% 2.60/1.35  tff(c_246, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_245])).
% 2.60/1.35  tff(c_44, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_118, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_44])).
% 2.60/1.35  tff(c_18, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.60/1.35  tff(c_30, plain, (![A_20]: (v4_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.35  tff(c_8, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.60/1.35  tff(c_63, plain, (![A_3]: (k1_subset_1(A_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8])).
% 2.60/1.35  tff(c_14, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=k2_subset_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.60/1.35  tff(c_62, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 2.60/1.35  tff(c_64, plain, (![A_6]: (k3_subset_1(A_6, '#skF_3')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62])).
% 2.60/1.35  tff(c_277, plain, (![B_77, A_78]: (v4_pre_topc(B_77, A_78) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_78), B_77), A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.60/1.35  tff(c_284, plain, (![A_78]: (v4_pre_topc('#skF_3', A_78) | ~v3_pre_topc(u1_struct_0(A_78), A_78) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(superposition, [status(thm), theory('equality')], [c_64, c_277])).
% 2.60/1.35  tff(c_289, plain, (![A_79]: (v4_pre_topc('#skF_3', A_79) | ~v3_pre_topc(u1_struct_0(A_79), A_79) | ~l1_pre_topc(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_284])).
% 2.60/1.35  tff(c_292, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_289])).
% 2.60/1.35  tff(c_294, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_292])).
% 2.60/1.35  tff(c_295, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_294])).
% 2.60/1.35  tff(c_221, plain, (![B_71, A_72]: (v4_pre_topc(B_71, A_72) | ~v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.35  tff(c_224, plain, (![B_71]: (v4_pre_topc(B_71, '#skF_1') | ~v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_221])).
% 2.60/1.35  tff(c_296, plain, (![B_80]: (v4_pre_topc(B_80, '#skF_1') | ~v1_xboole_0(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_224])).
% 2.60/1.35  tff(c_300, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_59, c_296])).
% 2.60/1.35  tff(c_307, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_300])).
% 2.60/1.35  tff(c_322, plain, (![A_83, B_84]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_83), B_84), A_83) | ~v4_pre_topc(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.60/1.35  tff(c_332, plain, (![A_83]: (v3_pre_topc(u1_struct_0(A_83), A_83) | ~v4_pre_topc('#skF_3', A_83) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(superposition, [status(thm), theory('equality')], [c_64, c_322])).
% 2.60/1.35  tff(c_338, plain, (![A_85]: (v3_pre_topc(u1_struct_0(A_85), A_85) | ~v4_pre_topc('#skF_3', A_85) | ~l1_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_332])).
% 2.60/1.35  tff(c_344, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_338])).
% 2.60/1.35  tff(c_347, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_307, c_344])).
% 2.60/1.35  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_347])).
% 2.60/1.35  tff(c_351, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_294])).
% 2.60/1.35  tff(c_58, plain, (![D_39]: (v3_pre_topc(D_39, '#skF_1') | ~r2_hidden(D_39, '#skF_3') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_124, plain, (![D_52]: (v3_pre_topc(D_52, '#skF_1') | ~r2_hidden(D_52, '#skF_3') | ~m1_subset_1(D_52, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_58])).
% 2.60/1.35  tff(c_134, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_61, c_124])).
% 2.60/1.35  tff(c_154, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_134])).
% 2.60/1.35  tff(c_52, plain, (![D_39]: (r2_hidden(D_39, '#skF_3') | ~r2_hidden('#skF_2', D_39) | ~v4_pre_topc(D_39, '#skF_1') | ~v3_pre_topc(D_39, '#skF_1') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.60/1.35  tff(c_248, plain, (![D_75]: (r2_hidden(D_75, '#skF_3') | ~r2_hidden('#skF_2', D_75) | ~v4_pre_topc(D_75, '#skF_1') | ~v3_pre_topc(D_75, '#skF_1') | ~m1_subset_1(D_75, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_52])).
% 2.60/1.35  tff(c_256, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_61, c_248])).
% 2.60/1.35  tff(c_262, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_154, c_256])).
% 2.60/1.35  tff(c_366, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_262])).
% 2.60/1.35  tff(c_367, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_366])).
% 2.60/1.35  tff(c_370, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_367])).
% 2.60/1.35  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_370])).
% 2.60/1.35  tff(c_375, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_366])).
% 2.60/1.35  tff(c_379, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_375])).
% 2.60/1.35  tff(c_382, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_379])).
% 2.60/1.35  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_382])).
% 2.60/1.35  tff(c_386, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_245])).
% 2.60/1.35  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.60/1.35  tff(c_66, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4])).
% 2.60/1.35  tff(c_390, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_386, c_66])).
% 2.60/1.35  tff(c_38, plain, (![A_27]: (~v2_tops_1(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.60/1.35  tff(c_402, plain, (~v2_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_390, c_38])).
% 2.60/1.35  tff(c_409, plain, (~v2_tops_1('#skF_3', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_402])).
% 2.60/1.35  tff(c_410, plain, (~v2_tops_1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_409])).
% 2.60/1.35  tff(c_465, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_218, c_410])).
% 2.60/1.35  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_465])).
% 2.60/1.35  tff(c_471, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_134])).
% 2.60/1.35  tff(c_22, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.35  tff(c_474, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_471, c_22])).
% 2.60/1.35  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_474])).
% 2.60/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.35  
% 2.60/1.35  Inference rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Ref     : 0
% 2.60/1.35  #Sup     : 70
% 2.60/1.35  #Fact    : 0
% 2.60/1.35  #Define  : 0
% 2.60/1.35  #Split   : 6
% 2.60/1.35  #Chain   : 0
% 2.60/1.35  #Close   : 0
% 2.60/1.35  
% 2.60/1.35  Ordering : KBO
% 2.60/1.35  
% 2.60/1.35  Simplification rules
% 2.60/1.35  ----------------------
% 2.60/1.35  #Subsume      : 11
% 2.60/1.35  #Demod        : 73
% 2.60/1.35  #Tautology    : 25
% 2.60/1.35  #SimpNegUnit  : 7
% 2.60/1.35  #BackRed      : 8
% 2.60/1.35  
% 2.60/1.35  #Partial instantiations: 0
% 2.60/1.35  #Strategies tried      : 1
% 2.60/1.35  
% 2.60/1.35  Timing (in seconds)
% 2.60/1.35  ----------------------
% 2.60/1.35  Preprocessing        : 0.32
% 2.60/1.35  Parsing              : 0.17
% 2.60/1.35  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.26
% 2.60/1.35  Inferencing          : 0.09
% 2.60/1.35  Reduction            : 0.09
% 2.60/1.35  Demodulation         : 0.06
% 2.60/1.35  BG Simplification    : 0.02
% 2.60/1.35  Subsumption          : 0.04
% 2.60/1.35  Abstraction          : 0.01
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.63
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
