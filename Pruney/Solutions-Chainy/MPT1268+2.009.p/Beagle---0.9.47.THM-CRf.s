%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 9.43s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 297 expanded)
%              Number of leaves         :   37 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  245 ( 800 expanded)
%              Number of equality atoms :   31 ( 128 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_96,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_800,plain,(
    ! [B_132,A_133] :
      ( v2_tops_1(B_132,A_133)
      | k1_tops_1(A_133,B_132) != k1_xboole_0
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_807,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_800])).

tff(c_811,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_807])).

tff(c_812,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_811])).

tff(c_681,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k1_tops_1(A_123,B_124),B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_686,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_681])).

tff(c_690,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_686])).

tff(c_282,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_290,plain,(
    ! [A_92] : r1_tarski(A_92,A_92) ),
    inference(resolution,[status(thm)],[c_282,c_6])).

tff(c_204,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_208,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_204])).

tff(c_422,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(A_100,C_101)
      | ~ r1_tarski(B_102,C_101)
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_466,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_107,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_208,c_422])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_707,plain,(
    ! [A_126,A_127] :
      ( r1_tarski(A_126,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_126,A_127)
      | ~ r1_tarski(A_127,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_466,c_12])).

tff(c_709,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_690,c_707])).

tff(c_722,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_709])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    ! [C_68] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_68
      | ~ v3_pre_topc(C_68,'#skF_3')
      | ~ r1_tarski(C_68,'#skF_4')
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_590,plain,(
    ! [C_118] :
      ( k1_xboole_0 = C_118
      | ~ v3_pre_topc(C_118,'#skF_3')
      | ~ r1_tarski(C_118,'#skF_4')
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_78])).

tff(c_1095,plain,(
    ! [A_154] :
      ( k1_xboole_0 = A_154
      | ~ v3_pre_topc(A_154,'#skF_3')
      | ~ r1_tarski(A_154,'#skF_4')
      | ~ r1_tarski(A_154,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_28,c_590])).

tff(c_1109,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_722,c_1095])).

tff(c_1132,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_1109])).

tff(c_1133,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_1132])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1160,plain,(
    ! [A_157,B_158] :
      ( v3_pre_topc(k1_tops_1(A_157,B_158),A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1165,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1160])).

tff(c_1169,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1165])).

tff(c_1171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1133,c_1169])).

tff(c_1172,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1173,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1175,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_62])).

tff(c_64,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1268,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_64])).

tff(c_66,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1275,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_66])).

tff(c_16,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1616,plain,(
    ! [A_200,B_201] :
      ( r1_tarski(k1_tops_1(A_200,B_201),B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2033,plain,(
    ! [A_234,A_235] :
      ( r1_tarski(k1_tops_1(A_234,A_235),A_235)
      | ~ l1_pre_topc(A_234)
      | ~ r1_tarski(A_235,u1_struct_0(A_234)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1616])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1301,plain,(
    ! [A_172,B_173] : k4_xboole_0(A_172,k4_xboole_0(A_172,B_173)) = k3_xboole_0(A_172,B_173) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1322,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1301])).

tff(c_1332,plain,(
    ! [A_176] : k4_xboole_0(A_176,A_176) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1322])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k4_xboole_0(B_16,A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1340,plain,(
    ! [A_176] :
      ( k1_xboole_0 = A_176
      | ~ r1_tarski(A_176,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1332,c_18])).

tff(c_2062,plain,(
    ! [A_234] :
      ( k1_tops_1(A_234,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_234)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_234)) ) ),
    inference(resolution,[status(thm)],[c_2033,c_1340])).

tff(c_2081,plain,(
    ! [A_236] :
      ( k1_tops_1(A_236,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2062])).

tff(c_2085,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_2081])).

tff(c_2337,plain,(
    ! [A_255,B_256,C_257] :
      ( r1_tarski('#skF_2'(A_255,B_256,C_257),C_257)
      | ~ r2_hidden(B_256,k1_tops_1(A_255,C_257))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2339,plain,(
    ! [B_256] :
      ( r1_tarski('#skF_2'('#skF_3',B_256,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_256,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_2337])).

tff(c_2349,plain,(
    ! [B_256] :
      ( r1_tarski('#skF_2'('#skF_3',B_256,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_256,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2339])).

tff(c_2828,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2349])).

tff(c_2831,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_2828])).

tff(c_2835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2831])).

tff(c_2870,plain,(
    ! [B_281] :
      ( r1_tarski('#skF_2'('#skF_3',B_281,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_281,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_2349])).

tff(c_1587,plain,(
    ! [A_196,C_197,B_198] :
      ( r1_tarski(A_196,C_197)
      | ~ r1_tarski(B_198,C_197)
      | ~ r1_tarski(A_196,B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1602,plain,(
    ! [A_196,A_14] :
      ( r1_tarski(A_196,A_14)
      | ~ r1_tarski(A_196,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_1587])).

tff(c_3078,plain,(
    ! [B_294,A_295] :
      ( r1_tarski('#skF_2'('#skF_3',B_294,k1_xboole_0),A_295)
      | ~ r2_hidden(B_294,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2870,c_1602])).

tff(c_2837,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2349])).

tff(c_38,plain,(
    ! [B_38,A_31,C_39] :
      ( r2_hidden(B_38,'#skF_2'(A_31,B_38,C_39))
      | ~ r2_hidden(B_38,k1_tops_1(A_31,C_39))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2091,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_2'('#skF_3',B_38,k1_xboole_0))
      | ~ r2_hidden(B_38,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_38])).

tff(c_2097,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_2'('#skF_3',B_38,k1_xboole_0))
      | ~ r2_hidden(B_38,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2091])).

tff(c_2969,plain,(
    ! [B_285] :
      ( r2_hidden(B_285,'#skF_2'('#skF_3',B_285,k1_xboole_0))
      | ~ r2_hidden(B_285,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2837,c_2097])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2976,plain,(
    ! [B_285] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_285,k1_xboole_0),B_285)
      | ~ r2_hidden(B_285,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2969,c_30])).

tff(c_3119,plain,(
    ! [A_295] : ~ r2_hidden(A_295,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3078,c_2976])).

tff(c_1690,plain,(
    ! [A_208,B_209] :
      ( k1_tops_1(A_208,B_209) = k1_xboole_0
      | ~ v2_tops_1(B_209,A_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1700,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1690])).

tff(c_1707,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1173,c_1700])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3187,plain,(
    ! [B_300,A_301,C_302,D_303] :
      ( r2_hidden(B_300,k1_tops_1(A_301,C_302))
      | ~ r2_hidden(B_300,D_303)
      | ~ r1_tarski(D_303,C_302)
      | ~ v3_pre_topc(D_303,A_301)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6289,plain,(
    ! [A_469,B_470,A_471,C_472] :
      ( r2_hidden('#skF_1'(A_469,B_470),k1_tops_1(A_471,C_472))
      | ~ r1_tarski(A_469,C_472)
      | ~ v3_pre_topc(A_469,A_471)
      | ~ m1_subset_1(A_469,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | r1_tarski(A_469,B_470) ) ),
    inference(resolution,[status(thm)],[c_8,c_3187])).

tff(c_6313,plain,(
    ! [A_469,B_470] :
      ( r2_hidden('#skF_1'(A_469,B_470),k1_xboole_0)
      | ~ r1_tarski(A_469,'#skF_4')
      | ~ v3_pre_topc(A_469,'#skF_3')
      | ~ m1_subset_1(A_469,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(A_469,B_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1707,c_6289])).

tff(c_6326,plain,(
    ! [A_469,B_470] :
      ( r2_hidden('#skF_1'(A_469,B_470),k1_xboole_0)
      | ~ r1_tarski(A_469,'#skF_4')
      | ~ v3_pre_topc(A_469,'#skF_3')
      | ~ m1_subset_1(A_469,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_469,B_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_6313])).

tff(c_6328,plain,(
    ! [A_473,B_474] :
      ( ~ r1_tarski(A_473,'#skF_4')
      | ~ v3_pre_topc(A_473,'#skF_3')
      | ~ m1_subset_1(A_473,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_473,B_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3119,c_6326])).

tff(c_6338,plain,(
    ! [B_474] :
      ( ~ r1_tarski('#skF_5','#skF_4')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | r1_tarski('#skF_5',B_474) ) ),
    inference(resolution,[status(thm)],[c_1275,c_6328])).

tff(c_6379,plain,(
    ! [B_475] : r1_tarski('#skF_5',B_475) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_1268,c_6338])).

tff(c_6448,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6379,c_1340])).

tff(c_6489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1172,c_6448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:05:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.43/3.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.43/3.55  
% 9.43/3.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.43/3.56  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 9.43/3.56  
% 9.43/3.56  %Foreground sorts:
% 9.43/3.56  
% 9.43/3.56  
% 9.43/3.56  %Background operators:
% 9.43/3.56  
% 9.43/3.56  
% 9.43/3.56  %Foreground operators:
% 9.43/3.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.43/3.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.43/3.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.43/3.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.43/3.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.43/3.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 9.43/3.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.43/3.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.43/3.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.43/3.56  tff('#skF_5', type, '#skF_5': $i).
% 9.43/3.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.43/3.56  tff('#skF_3', type, '#skF_3': $i).
% 9.43/3.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.43/3.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.43/3.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.43/3.56  tff('#skF_4', type, '#skF_4': $i).
% 9.43/3.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.43/3.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.43/3.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.43/3.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.43/3.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.43/3.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.43/3.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.43/3.56  
% 9.58/3.59  tff(f_147, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 9.58/3.59  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 9.58/3.59  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 9.58/3.59  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.58/3.59  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.58/3.59  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.58/3.59  tff(f_73, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.58/3.59  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.58/3.59  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.58/3.59  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.58/3.59  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.58/3.59  tff(f_50, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 9.58/3.59  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 9.58/3.59  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.58/3.59  tff(c_60, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_96, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 9.58/3.59  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_800, plain, (![B_132, A_133]: (v2_tops_1(B_132, A_133) | k1_tops_1(A_133, B_132)!=k1_xboole_0 | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.58/3.59  tff(c_807, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_800])).
% 9.58/3.59  tff(c_811, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_807])).
% 9.58/3.59  tff(c_812, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_96, c_811])).
% 9.58/3.59  tff(c_681, plain, (![A_123, B_124]: (r1_tarski(k1_tops_1(A_123, B_124), B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.58/3.59  tff(c_686, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_681])).
% 9.58/3.59  tff(c_690, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_686])).
% 9.58/3.59  tff(c_282, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), A_92) | r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.58/3.59  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.58/3.59  tff(c_290, plain, (![A_92]: (r1_tarski(A_92, A_92))), inference(resolution, [status(thm)], [c_282, c_6])).
% 9.58/3.59  tff(c_204, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.58/3.59  tff(c_208, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_204])).
% 9.58/3.59  tff(c_422, plain, (![A_100, C_101, B_102]: (r1_tarski(A_100, C_101) | ~r1_tarski(B_102, C_101) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.58/3.59  tff(c_466, plain, (![A_107]: (r1_tarski(A_107, u1_struct_0('#skF_3')) | ~r1_tarski(A_107, '#skF_4'))), inference(resolution, [status(thm)], [c_208, c_422])).
% 9.58/3.59  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.58/3.59  tff(c_707, plain, (![A_126, A_127]: (r1_tarski(A_126, u1_struct_0('#skF_3')) | ~r1_tarski(A_126, A_127) | ~r1_tarski(A_127, '#skF_4'))), inference(resolution, [status(thm)], [c_466, c_12])).
% 9.58/3.59  tff(c_709, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_690, c_707])).
% 9.58/3.59  tff(c_722, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_709])).
% 9.58/3.59  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.58/3.59  tff(c_78, plain, (![C_68]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_68 | ~v3_pre_topc(C_68, '#skF_3') | ~r1_tarski(C_68, '#skF_4') | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_590, plain, (![C_118]: (k1_xboole_0=C_118 | ~v3_pre_topc(C_118, '#skF_3') | ~r1_tarski(C_118, '#skF_4') | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_96, c_78])).
% 9.58/3.59  tff(c_1095, plain, (![A_154]: (k1_xboole_0=A_154 | ~v3_pre_topc(A_154, '#skF_3') | ~r1_tarski(A_154, '#skF_4') | ~r1_tarski(A_154, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_28, c_590])).
% 9.58/3.59  tff(c_1109, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_722, c_1095])).
% 9.58/3.59  tff(c_1132, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_690, c_1109])).
% 9.58/3.59  tff(c_1133, plain, (~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_812, c_1132])).
% 9.58/3.59  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_1160, plain, (![A_157, B_158]: (v3_pre_topc(k1_tops_1(A_157, B_158), A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.58/3.59  tff(c_1165, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1160])).
% 9.58/3.59  tff(c_1169, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1165])).
% 9.58/3.59  tff(c_1171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1133, c_1169])).
% 9.58/3.59  tff(c_1172, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 9.58/3.59  tff(c_1173, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 9.58/3.59  tff(c_62, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_1175, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_62])).
% 9.58/3.59  tff(c_64, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_1268, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_64])).
% 9.58/3.59  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.58/3.59  tff(c_1275, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_66])).
% 9.58/3.59  tff(c_16, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.58/3.59  tff(c_1616, plain, (![A_200, B_201]: (r1_tarski(k1_tops_1(A_200, B_201), B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.58/3.59  tff(c_2033, plain, (![A_234, A_235]: (r1_tarski(k1_tops_1(A_234, A_235), A_235) | ~l1_pre_topc(A_234) | ~r1_tarski(A_235, u1_struct_0(A_234)))), inference(resolution, [status(thm)], [c_28, c_1616])).
% 9.58/3.59  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.58/3.59  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.58/3.59  tff(c_1301, plain, (![A_172, B_173]: (k4_xboole_0(A_172, k4_xboole_0(A_172, B_173))=k3_xboole_0(A_172, B_173))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.58/3.59  tff(c_1322, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1301])).
% 9.58/3.59  tff(c_1332, plain, (![A_176]: (k4_xboole_0(A_176, A_176)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1322])).
% 9.58/3.59  tff(c_18, plain, (![A_15, B_16]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k4_xboole_0(B_16, A_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.58/3.59  tff(c_1340, plain, (![A_176]: (k1_xboole_0=A_176 | ~r1_tarski(A_176, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1332, c_18])).
% 9.58/3.59  tff(c_2062, plain, (![A_234]: (k1_tops_1(A_234, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_234) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_234)))), inference(resolution, [status(thm)], [c_2033, c_1340])).
% 9.58/3.59  tff(c_2081, plain, (![A_236]: (k1_tops_1(A_236, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2062])).
% 9.58/3.59  tff(c_2085, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_2081])).
% 9.58/3.59  tff(c_2337, plain, (![A_255, B_256, C_257]: (r1_tarski('#skF_2'(A_255, B_256, C_257), C_257) | ~r2_hidden(B_256, k1_tops_1(A_255, C_257)) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.58/3.59  tff(c_2339, plain, (![B_256]: (r1_tarski('#skF_2'('#skF_3', B_256, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_256, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2085, c_2337])).
% 9.58/3.59  tff(c_2349, plain, (![B_256]: (r1_tarski('#skF_2'('#skF_3', B_256, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_256, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2339])).
% 9.58/3.59  tff(c_2828, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2349])).
% 9.58/3.59  tff(c_2831, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_2828])).
% 9.58/3.59  tff(c_2835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_2831])).
% 9.58/3.59  tff(c_2870, plain, (![B_281]: (r1_tarski('#skF_2'('#skF_3', B_281, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_281, k1_xboole_0))), inference(splitRight, [status(thm)], [c_2349])).
% 9.58/3.59  tff(c_1587, plain, (![A_196, C_197, B_198]: (r1_tarski(A_196, C_197) | ~r1_tarski(B_198, C_197) | ~r1_tarski(A_196, B_198))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.58/3.59  tff(c_1602, plain, (![A_196, A_14]: (r1_tarski(A_196, A_14) | ~r1_tarski(A_196, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_1587])).
% 9.58/3.59  tff(c_3078, plain, (![B_294, A_295]: (r1_tarski('#skF_2'('#skF_3', B_294, k1_xboole_0), A_295) | ~r2_hidden(B_294, k1_xboole_0))), inference(resolution, [status(thm)], [c_2870, c_1602])).
% 9.58/3.59  tff(c_2837, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2349])).
% 9.58/3.59  tff(c_38, plain, (![B_38, A_31, C_39]: (r2_hidden(B_38, '#skF_2'(A_31, B_38, C_39)) | ~r2_hidden(B_38, k1_tops_1(A_31, C_39)) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.58/3.59  tff(c_2091, plain, (![B_38]: (r2_hidden(B_38, '#skF_2'('#skF_3', B_38, k1_xboole_0)) | ~r2_hidden(B_38, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2085, c_38])).
% 9.58/3.59  tff(c_2097, plain, (![B_38]: (r2_hidden(B_38, '#skF_2'('#skF_3', B_38, k1_xboole_0)) | ~r2_hidden(B_38, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2091])).
% 9.58/3.59  tff(c_2969, plain, (![B_285]: (r2_hidden(B_285, '#skF_2'('#skF_3', B_285, k1_xboole_0)) | ~r2_hidden(B_285, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2837, c_2097])).
% 9.58/3.59  tff(c_30, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.58/3.59  tff(c_2976, plain, (![B_285]: (~r1_tarski('#skF_2'('#skF_3', B_285, k1_xboole_0), B_285) | ~r2_hidden(B_285, k1_xboole_0))), inference(resolution, [status(thm)], [c_2969, c_30])).
% 9.58/3.59  tff(c_3119, plain, (![A_295]: (~r2_hidden(A_295, k1_xboole_0))), inference(resolution, [status(thm)], [c_3078, c_2976])).
% 9.58/3.59  tff(c_1690, plain, (![A_208, B_209]: (k1_tops_1(A_208, B_209)=k1_xboole_0 | ~v2_tops_1(B_209, A_208) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.58/3.59  tff(c_1700, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1690])).
% 9.58/3.59  tff(c_1707, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1173, c_1700])).
% 9.58/3.59  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.58/3.59  tff(c_3187, plain, (![B_300, A_301, C_302, D_303]: (r2_hidden(B_300, k1_tops_1(A_301, C_302)) | ~r2_hidden(B_300, D_303) | ~r1_tarski(D_303, C_302) | ~v3_pre_topc(D_303, A_301) | ~m1_subset_1(D_303, k1_zfmisc_1(u1_struct_0(A_301))) | ~m1_subset_1(C_302, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.58/3.59  tff(c_6289, plain, (![A_469, B_470, A_471, C_472]: (r2_hidden('#skF_1'(A_469, B_470), k1_tops_1(A_471, C_472)) | ~r1_tarski(A_469, C_472) | ~v3_pre_topc(A_469, A_471) | ~m1_subset_1(A_469, k1_zfmisc_1(u1_struct_0(A_471))) | ~m1_subset_1(C_472, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | r1_tarski(A_469, B_470))), inference(resolution, [status(thm)], [c_8, c_3187])).
% 9.58/3.59  tff(c_6313, plain, (![A_469, B_470]: (r2_hidden('#skF_1'(A_469, B_470), k1_xboole_0) | ~r1_tarski(A_469, '#skF_4') | ~v3_pre_topc(A_469, '#skF_3') | ~m1_subset_1(A_469, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(A_469, B_470))), inference(superposition, [status(thm), theory('equality')], [c_1707, c_6289])).
% 9.58/3.59  tff(c_6326, plain, (![A_469, B_470]: (r2_hidden('#skF_1'(A_469, B_470), k1_xboole_0) | ~r1_tarski(A_469, '#skF_4') | ~v3_pre_topc(A_469, '#skF_3') | ~m1_subset_1(A_469, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_469, B_470))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_6313])).
% 9.58/3.59  tff(c_6328, plain, (![A_473, B_474]: (~r1_tarski(A_473, '#skF_4') | ~v3_pre_topc(A_473, '#skF_3') | ~m1_subset_1(A_473, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_473, B_474))), inference(negUnitSimplification, [status(thm)], [c_3119, c_6326])).
% 9.58/3.59  tff(c_6338, plain, (![B_474]: (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | r1_tarski('#skF_5', B_474))), inference(resolution, [status(thm)], [c_1275, c_6328])).
% 9.58/3.59  tff(c_6379, plain, (![B_475]: (r1_tarski('#skF_5', B_475))), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_1268, c_6338])).
% 9.58/3.59  tff(c_6448, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_6379, c_1340])).
% 9.58/3.59  tff(c_6489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1172, c_6448])).
% 9.58/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.59  
% 9.58/3.59  Inference rules
% 9.58/3.59  ----------------------
% 9.58/3.59  #Ref     : 0
% 9.58/3.59  #Sup     : 1397
% 9.58/3.59  #Fact    : 0
% 9.58/3.59  #Define  : 0
% 9.58/3.59  #Split   : 15
% 9.58/3.59  #Chain   : 0
% 9.58/3.59  #Close   : 0
% 9.58/3.59  
% 9.58/3.59  Ordering : KBO
% 9.58/3.59  
% 9.58/3.59  Simplification rules
% 9.58/3.59  ----------------------
% 9.58/3.59  #Subsume      : 342
% 9.58/3.59  #Demod        : 1354
% 9.58/3.59  #Tautology    : 577
% 9.58/3.59  #SimpNegUnit  : 24
% 9.58/3.59  #BackRed      : 15
% 9.58/3.59  
% 9.58/3.59  #Partial instantiations: 0
% 9.58/3.59  #Strategies tried      : 1
% 9.58/3.59  
% 9.58/3.59  Timing (in seconds)
% 9.58/3.59  ----------------------
% 9.58/3.59  Preprocessing        : 0.53
% 9.58/3.59  Parsing              : 0.27
% 9.58/3.59  CNF conversion       : 0.04
% 9.58/3.59  Main loop            : 2.12
% 9.58/3.59  Inferencing          : 0.68
% 9.58/3.59  Reduction            : 0.80
% 9.58/3.59  Demodulation         : 0.61
% 9.58/3.59  BG Simplification    : 0.07
% 9.58/3.60  Subsumption          : 0.43
% 9.58/3.60  Abstraction          : 0.08
% 9.58/3.60  MUC search           : 0.00
% 9.58/3.60  Cooper               : 0.00
% 9.58/3.60  Total                : 2.72
% 9.58/3.60  Index Insertion      : 0.00
% 9.58/3.60  Index Deletion       : 0.00
% 9.58/3.60  Index Matching       : 0.00
% 9.58/3.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
