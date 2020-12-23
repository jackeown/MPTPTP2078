%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:08 EST 2020

% Result     : Theorem 8.33s
% Output     : CNFRefutation 8.33s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 216 expanded)
%              Number of leaves         :   34 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 572 expanded)
%              Number of equality atoms :   47 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_70,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_118,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    ! [C_42,A_30,D_44,B_38] :
      ( v3_pre_topc(C_42,A_30)
      | k1_tops_1(A_30,C_42) != C_42
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(B_38)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(B_38)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5196,plain,(
    ! [D_351,B_352] :
      ( ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0(B_352)))
      | ~ l1_pre_topc(B_352) ) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_5199,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_5196])).

tff(c_5203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5199])).

tff(c_5496,plain,(
    ! [C_371,A_372] :
      ( v3_pre_topc(C_371,A_372)
      | k1_tops_1(A_372,C_371) != C_371
      | ~ m1_subset_1(C_371,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5502,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_5496])).

tff(c_5506,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5502])).

tff(c_5507,plain,(
    k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5506])).

tff(c_186,plain,(
    ! [A_81,B_82,C_83] :
      ( k7_subset_1(A_81,B_82,C_83) = k4_xboole_0(B_82,C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_189,plain,(
    ! [C_83] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_83) = k4_xboole_0('#skF_6',C_83) ),
    inference(resolution,[status(thm)],[c_64,c_186])).

tff(c_650,plain,(
    ! [A_120,B_121] :
      ( k7_subset_1(u1_struct_0(A_120),B_121,k2_tops_1(A_120,B_121)) = k1_tops_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_654,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_650])).

tff(c_658,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_189,c_654])).

tff(c_36,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_3'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3971,plain,(
    ! [A_284,B_285,C_286] :
      ( r2_hidden('#skF_3'(A_284,B_285,C_286),A_284)
      | r2_hidden('#skF_4'(A_284,B_285,C_286),B_285)
      | ~ r2_hidden('#skF_4'(A_284,B_285,C_286),A_284)
      | k4_xboole_0(A_284,B_285) = C_286 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4003,plain,(
    ! [C_9,B_8] :
      ( r2_hidden('#skF_4'(C_9,B_8,C_9),B_8)
      | r2_hidden('#skF_3'(C_9,B_8,C_9),C_9)
      | k4_xboole_0(C_9,B_8) = C_9 ) ),
    inference(resolution,[status(thm)],[c_36,c_3971])).

tff(c_32,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4920,plain,(
    ! [C_340,B_341] :
      ( r2_hidden('#skF_4'(C_340,B_341,C_340),B_341)
      | r2_hidden('#skF_3'(C_340,B_341,C_340),C_340)
      | k4_xboole_0(C_340,B_341) = C_340 ) ),
    inference(resolution,[status(thm)],[c_36,c_3971])).

tff(c_26,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),B_8)
      | ~ r2_hidden('#skF_4'(A_7,B_8,C_9),A_7)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5075,plain,(
    ! [C_344,B_345] :
      ( ~ r2_hidden('#skF_4'(C_344,B_345,C_344),C_344)
      | r2_hidden('#skF_4'(C_344,B_345,C_344),B_345)
      | k4_xboole_0(C_344,B_345) = C_344 ) ),
    inference(resolution,[status(thm)],[c_4920,c_26])).

tff(c_7982,plain,(
    ! [C_467,B_468] :
      ( r2_hidden('#skF_4'(C_467,B_468,C_467),B_468)
      | ~ r2_hidden('#skF_3'(C_467,B_468,C_467),C_467)
      | k4_xboole_0(C_467,B_468) = C_467 ) ),
    inference(resolution,[status(thm)],[c_32,c_5075])).

tff(c_8012,plain,(
    ! [C_469,B_470] :
      ( r2_hidden('#skF_4'(C_469,B_470,C_469),B_470)
      | k4_xboole_0(C_469,B_470) = C_469 ) ),
    inference(resolution,[status(thm)],[c_4003,c_7982])).

tff(c_199,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k2_pre_topc(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [A_20,B_21,C_22] :
      ( k7_subset_1(A_20,B_21,C_22) = k4_xboole_0(B_21,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6094,plain,(
    ! [A_405,B_406,C_407] :
      ( k7_subset_1(u1_struct_0(A_405),k2_pre_topc(A_405,B_406),C_407) = k4_xboole_0(k2_pre_topc(A_405,B_406),C_407)
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ l1_pre_topc(A_405) ) ),
    inference(resolution,[status(thm)],[c_199,c_50])).

tff(c_6098,plain,(
    ! [C_407] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_407) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_407)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_6094])).

tff(c_6110,plain,(
    ! [C_409] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_409) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_409) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6098])).

tff(c_76,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_169,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_76])).

tff(c_6120,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6110,c_169])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6167,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_6')
      | ~ r2_hidden(D_12,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6120,c_22])).

tff(c_8445,plain,(
    ! [C_488] :
      ( ~ r2_hidden('#skF_4'(C_488,k2_tops_1('#skF_5','#skF_6'),C_488),'#skF_6')
      | k4_xboole_0(C_488,k2_tops_1('#skF_5','#skF_6')) = C_488 ) ),
    inference(resolution,[status(thm)],[c_8012,c_6167])).

tff(c_8449,plain,
    ( r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_36,c_8445])).

tff(c_8455,plain,
    ( r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_8449])).

tff(c_8456,plain,(
    r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_5507,c_8455])).

tff(c_8453,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_8445])).

tff(c_8458,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_8453])).

tff(c_8459,plain,(
    ~ r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_5507,c_8458])).

tff(c_8466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8456,c_8459])).

tff(c_8467,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_8468,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_60,plain,(
    ! [B_38,D_44,C_42,A_30] :
      ( k1_tops_1(B_38,D_44) = D_44
      | ~ v3_pre_topc(D_44,B_38)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(B_38)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(B_38)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_13682,plain,(
    ! [C_820,A_821] :
      ( ~ m1_subset_1(C_820,k1_zfmisc_1(u1_struct_0(A_821)))
      | ~ l1_pre_topc(A_821)
      | ~ v2_pre_topc(A_821) ) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_13688,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_13682])).

tff(c_13693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_13688])).

tff(c_13695,plain,(
    ! [B_822,D_823] :
      ( k1_tops_1(B_822,D_823) = D_823
      | ~ v3_pre_topc(D_823,B_822)
      | ~ m1_subset_1(D_823,k1_zfmisc_1(u1_struct_0(B_822)))
      | ~ l1_pre_topc(B_822) ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_13701,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_13695])).

tff(c_13705,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8468,c_13701])).

tff(c_56,plain,(
    ! [A_27,B_29] :
      ( k7_subset_1(u1_struct_0(A_27),k2_pre_topc(A_27,B_29),k1_tops_1(A_27,B_29)) = k2_tops_1(A_27,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_13729,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13705,c_56])).

tff(c_13733,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_13729])).

tff(c_13735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8467,c_13733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:17:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.33/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/2.96  
% 8.33/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/2.96  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 8.33/2.96  
% 8.33/2.96  %Foreground sorts:
% 8.33/2.96  
% 8.33/2.96  
% 8.33/2.96  %Background operators:
% 8.33/2.96  
% 8.33/2.96  
% 8.33/2.96  %Foreground operators:
% 8.33/2.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.33/2.96  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.33/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.33/2.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.33/2.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.33/2.96  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.33/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.33/2.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.33/2.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.33/2.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.33/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.33/2.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.33/2.96  tff('#skF_5', type, '#skF_5': $i).
% 8.33/2.96  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.33/2.96  tff('#skF_6', type, '#skF_6': $i).
% 8.33/2.96  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.33/2.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.33/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.33/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.33/2.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.33/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.33/2.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.33/2.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.33/2.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.33/2.96  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.33/2.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.33/2.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.33/2.96  
% 8.33/2.97  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 8.33/2.97  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 8.33/2.97  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.33/2.97  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 8.33/2.97  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.33/2.97  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.33/2.97  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.33/2.97  tff(c_70, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.33/2.97  tff(c_118, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 8.33/2.97  tff(c_68, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.33/2.97  tff(c_66, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.33/2.97  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.33/2.97  tff(c_58, plain, (![C_42, A_30, D_44, B_38]: (v3_pre_topc(C_42, A_30) | k1_tops_1(A_30, C_42)!=C_42 | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(B_38))) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(B_38) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.33/2.97  tff(c_5196, plain, (![D_351, B_352]: (~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0(B_352))) | ~l1_pre_topc(B_352))), inference(splitLeft, [status(thm)], [c_58])).
% 8.33/2.97  tff(c_5199, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_5196])).
% 8.33/2.97  tff(c_5203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_5199])).
% 8.33/2.97  tff(c_5496, plain, (![C_371, A_372]: (v3_pre_topc(C_371, A_372) | k1_tops_1(A_372, C_371)!=C_371 | ~m1_subset_1(C_371, k1_zfmisc_1(u1_struct_0(A_372))) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372))), inference(splitRight, [status(thm)], [c_58])).
% 8.33/2.97  tff(c_5502, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_5496])).
% 8.33/2.97  tff(c_5506, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5502])).
% 8.33/2.97  tff(c_5507, plain, (k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_118, c_5506])).
% 8.33/2.97  tff(c_186, plain, (![A_81, B_82, C_83]: (k7_subset_1(A_81, B_82, C_83)=k4_xboole_0(B_82, C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.33/2.97  tff(c_189, plain, (![C_83]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_83)=k4_xboole_0('#skF_6', C_83))), inference(resolution, [status(thm)], [c_64, c_186])).
% 8.33/2.97  tff(c_650, plain, (![A_120, B_121]: (k7_subset_1(u1_struct_0(A_120), B_121, k2_tops_1(A_120, B_121))=k1_tops_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.33/2.97  tff(c_654, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_650])).
% 8.33/2.97  tff(c_658, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_189, c_654])).
% 8.33/2.97  tff(c_36, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_3'(A_7, B_8, C_9), A_7) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.33/2.97  tff(c_3971, plain, (![A_284, B_285, C_286]: (r2_hidden('#skF_3'(A_284, B_285, C_286), A_284) | r2_hidden('#skF_4'(A_284, B_285, C_286), B_285) | ~r2_hidden('#skF_4'(A_284, B_285, C_286), A_284) | k4_xboole_0(A_284, B_285)=C_286)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.33/2.97  tff(c_4003, plain, (![C_9, B_8]: (r2_hidden('#skF_4'(C_9, B_8, C_9), B_8) | r2_hidden('#skF_3'(C_9, B_8, C_9), C_9) | k4_xboole_0(C_9, B_8)=C_9)), inference(resolution, [status(thm)], [c_36, c_3971])).
% 8.33/2.97  tff(c_32, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), C_9) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.33/2.97  tff(c_4920, plain, (![C_340, B_341]: (r2_hidden('#skF_4'(C_340, B_341, C_340), B_341) | r2_hidden('#skF_3'(C_340, B_341, C_340), C_340) | k4_xboole_0(C_340, B_341)=C_340)), inference(resolution, [status(thm)], [c_36, c_3971])).
% 8.33/2.97  tff(c_26, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), C_9) | r2_hidden('#skF_4'(A_7, B_8, C_9), B_8) | ~r2_hidden('#skF_4'(A_7, B_8, C_9), A_7) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.33/2.97  tff(c_5075, plain, (![C_344, B_345]: (~r2_hidden('#skF_4'(C_344, B_345, C_344), C_344) | r2_hidden('#skF_4'(C_344, B_345, C_344), B_345) | k4_xboole_0(C_344, B_345)=C_344)), inference(resolution, [status(thm)], [c_4920, c_26])).
% 8.33/2.97  tff(c_7982, plain, (![C_467, B_468]: (r2_hidden('#skF_4'(C_467, B_468, C_467), B_468) | ~r2_hidden('#skF_3'(C_467, B_468, C_467), C_467) | k4_xboole_0(C_467, B_468)=C_467)), inference(resolution, [status(thm)], [c_32, c_5075])).
% 8.33/2.97  tff(c_8012, plain, (![C_469, B_470]: (r2_hidden('#skF_4'(C_469, B_470, C_469), B_470) | k4_xboole_0(C_469, B_470)=C_469)), inference(resolution, [status(thm)], [c_4003, c_7982])).
% 8.33/2.97  tff(c_199, plain, (![A_85, B_86]: (m1_subset_1(k2_pre_topc(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.33/2.97  tff(c_50, plain, (![A_20, B_21, C_22]: (k7_subset_1(A_20, B_21, C_22)=k4_xboole_0(B_21, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.33/2.97  tff(c_6094, plain, (![A_405, B_406, C_407]: (k7_subset_1(u1_struct_0(A_405), k2_pre_topc(A_405, B_406), C_407)=k4_xboole_0(k2_pre_topc(A_405, B_406), C_407) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_405))) | ~l1_pre_topc(A_405))), inference(resolution, [status(thm)], [c_199, c_50])).
% 8.33/2.97  tff(c_6098, plain, (![C_407]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_407)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_407) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_6094])).
% 8.33/2.97  tff(c_6110, plain, (![C_409]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_409)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_409))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6098])).
% 8.33/2.97  tff(c_76, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.33/2.97  tff(c_169, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_118, c_76])).
% 8.33/2.97  tff(c_6120, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6110, c_169])).
% 8.33/2.97  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.33/2.97  tff(c_6167, plain, (![D_12]: (~r2_hidden(D_12, '#skF_6') | ~r2_hidden(D_12, k2_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_6120, c_22])).
% 8.33/2.97  tff(c_8445, plain, (![C_488]: (~r2_hidden('#skF_4'(C_488, k2_tops_1('#skF_5', '#skF_6'), C_488), '#skF_6') | k4_xboole_0(C_488, k2_tops_1('#skF_5', '#skF_6'))=C_488)), inference(resolution, [status(thm)], [c_8012, c_6167])).
% 8.33/2.97  tff(c_8449, plain, (r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_36, c_8445])).
% 8.33/2.97  tff(c_8455, plain, (r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_8449])).
% 8.33/2.97  tff(c_8456, plain, (r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_5507, c_8455])).
% 8.33/2.97  tff(c_8453, plain, (~r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_32, c_8445])).
% 8.33/2.97  tff(c_8458, plain, (~r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_8453])).
% 8.33/2.97  tff(c_8459, plain, (~r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_5507, c_8458])).
% 8.33/2.97  tff(c_8466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8456, c_8459])).
% 8.33/2.97  tff(c_8467, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 8.33/2.97  tff(c_8468, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 8.33/2.97  tff(c_60, plain, (![B_38, D_44, C_42, A_30]: (k1_tops_1(B_38, D_44)=D_44 | ~v3_pre_topc(D_44, B_38) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(B_38))) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(B_38) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.33/2.97  tff(c_13682, plain, (![C_820, A_821]: (~m1_subset_1(C_820, k1_zfmisc_1(u1_struct_0(A_821))) | ~l1_pre_topc(A_821) | ~v2_pre_topc(A_821))), inference(splitLeft, [status(thm)], [c_60])).
% 8.33/2.97  tff(c_13688, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_13682])).
% 8.33/2.97  tff(c_13693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_13688])).
% 8.33/2.97  tff(c_13695, plain, (![B_822, D_823]: (k1_tops_1(B_822, D_823)=D_823 | ~v3_pre_topc(D_823, B_822) | ~m1_subset_1(D_823, k1_zfmisc_1(u1_struct_0(B_822))) | ~l1_pre_topc(B_822))), inference(splitRight, [status(thm)], [c_60])).
% 8.33/2.97  tff(c_13701, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_13695])).
% 8.33/2.97  tff(c_13705, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8468, c_13701])).
% 8.33/2.97  tff(c_56, plain, (![A_27, B_29]: (k7_subset_1(u1_struct_0(A_27), k2_pre_topc(A_27, B_29), k1_tops_1(A_27, B_29))=k2_tops_1(A_27, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.33/2.97  tff(c_13729, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13705, c_56])).
% 8.33/2.97  tff(c_13733, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_13729])).
% 8.33/2.97  tff(c_13735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8467, c_13733])).
% 8.33/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/2.97  
% 8.33/2.97  Inference rules
% 8.33/2.97  ----------------------
% 8.33/2.97  #Ref     : 0
% 8.33/2.97  #Sup     : 2819
% 8.33/2.97  #Fact    : 0
% 8.33/2.97  #Define  : 0
% 8.33/2.97  #Split   : 18
% 8.33/2.97  #Chain   : 0
% 8.33/2.97  #Close   : 0
% 8.33/2.97  
% 8.33/2.97  Ordering : KBO
% 8.33/2.97  
% 8.33/2.97  Simplification rules
% 8.33/2.97  ----------------------
% 8.33/2.97  #Subsume      : 607
% 8.33/2.97  #Demod        : 1979
% 8.33/2.97  #Tautology    : 1074
% 8.33/2.97  #SimpNegUnit  : 70
% 8.33/2.97  #BackRed      : 96
% 8.33/2.97  
% 8.33/2.97  #Partial instantiations: 0
% 8.33/2.97  #Strategies tried      : 1
% 8.33/2.97  
% 8.33/2.97  Timing (in seconds)
% 8.33/2.97  ----------------------
% 8.33/2.98  Preprocessing        : 0.35
% 8.33/2.98  Parsing              : 0.18
% 8.33/2.98  CNF conversion       : 0.03
% 8.33/2.98  Main loop            : 1.84
% 8.33/2.98  Inferencing          : 0.63
% 8.33/2.98  Reduction            : 0.59
% 8.33/2.98  Demodulation         : 0.42
% 8.33/2.98  BG Simplification    : 0.07
% 8.33/2.98  Subsumption          : 0.41
% 8.33/2.98  Abstraction          : 0.10
% 8.33/2.98  MUC search           : 0.00
% 8.33/2.98  Cooper               : 0.00
% 8.33/2.98  Total                : 2.23
% 8.33/2.98  Index Insertion      : 0.00
% 8.33/2.98  Index Deletion       : 0.00
% 8.33/2.98  Index Matching       : 0.00
% 8.33/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
