%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:07 EST 2020

% Result     : Theorem 10.21s
% Output     : CNFRefutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 535 expanded)
%              Number of leaves         :   38 ( 195 expanded)
%              Depth                    :   18
%              Number of atoms          :  215 (1042 expanded)
%              Number of equality atoms :   93 ( 348 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_127,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_122,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    ! [C_54,A_42,D_56,B_50] :
      ( v3_pre_topc(C_54,A_42)
      | k1_tops_1(A_42,C_54) != C_54
      | ~ m1_subset_1(D_56,k1_zfmisc_1(u1_struct_0(B_50)))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(B_50)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5497,plain,(
    ! [D_221,B_222] :
      ( ~ m1_subset_1(D_221,k1_zfmisc_1(u1_struct_0(B_222)))
      | ~ l1_pre_topc(B_222) ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_5511,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_5497])).

tff(c_5521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5511])).

tff(c_5669,plain,(
    ! [C_225,A_226] :
      ( v3_pre_topc(C_225,A_226)
      | k1_tops_1(A_226,C_225) != C_225
      | ~ m1_subset_1(C_225,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5687,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_5669])).

tff(c_5698,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5687])).

tff(c_5699,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_5698])).

tff(c_1174,plain,(
    ! [B_146,A_147] :
      ( r1_tarski(B_146,k2_pre_topc(A_147,B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1185,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1174])).

tff(c_1194,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1185])).

tff(c_1443,plain,(
    ! [A_164,B_165] :
      ( m1_subset_1(k2_pre_topc(A_164,B_165),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_subset_1(A_16,B_17,C_18) = k4_xboole_0(B_17,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17129,plain,(
    ! [A_362,B_363,C_364] :
      ( k7_subset_1(u1_struct_0(A_362),k2_pre_topc(A_362,B_363),C_364) = k4_xboole_0(k2_pre_topc(A_362,B_363),C_364)
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ l1_pre_topc(A_362) ) ),
    inference(resolution,[status(thm)],[c_1443,c_22])).

tff(c_17142,plain,(
    ! [C_364] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_364) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_364)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_17129])).

tff(c_17380,plain,(
    ! [C_367] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_367) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_17142])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_224,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_62])).

tff(c_17401,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17380,c_224])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_629,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_643,plain,(
    ! [B_28,A_27] :
      ( k4_xboole_0(B_28,A_27) = k3_subset_1(B_28,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_32,c_629])).

tff(c_1202,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1194,c_643])).

tff(c_17480,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17401,c_1202])).

tff(c_440,plain,(
    ! [A_95,B_96] :
      ( k3_subset_1(A_95,k3_subset_1(A_95,B_96)) = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_447,plain,(
    ! [B_28,A_27] :
      ( k3_subset_1(B_28,k3_subset_1(B_28,A_27)) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_32,c_440])).

tff(c_17547,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17480,c_447])).

tff(c_17558,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_17547])).

tff(c_42,plain,(
    ! [A_39,B_41] :
      ( k7_subset_1(u1_struct_0(A_39),k2_pre_topc(A_39,B_41),k1_tops_1(A_39,B_41)) = k2_tops_1(A_39,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17398,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17380,c_42])).

tff(c_17425,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_17398])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_747,plain,(
    ! [B_116,A_117] :
      ( k4_xboole_0(B_116,A_117) = k3_subset_1(B_116,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(resolution,[status(thm)],[c_32,c_629])).

tff(c_768,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_10,c_747])).

tff(c_782,plain,(
    ! [A_5,B_6] : k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_768])).

tff(c_18468,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17425,c_782])).

tff(c_18487,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17558,c_18468])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_641,plain,(
    ! [A_26] : k4_xboole_0(A_26,k1_xboole_0) = k3_subset_1(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_629])).

tff(c_646,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_641])).

tff(c_1027,plain,(
    ! [A_132,B_133,C_134] :
      ( k7_subset_1(A_132,B_133,C_134) = k4_xboole_0(B_133,C_134)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1041,plain,(
    ! [C_134] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_134) = k4_xboole_0('#skF_2',C_134) ),
    inference(resolution,[status(thm)],[c_50,c_1027])).

tff(c_2057,plain,(
    ! [A_180,B_181] :
      ( k7_subset_1(u1_struct_0(A_180),B_181,k2_tops_1(A_180,B_181)) = k1_tops_1(A_180,B_181)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2070,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2057])).

tff(c_2081,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1041,c_2070])).

tff(c_449,plain,(
    ! [A_26] : k3_subset_1(A_26,k3_subset_1(A_26,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_440])).

tff(c_648,plain,(
    ! [A_26] : k3_subset_1(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_449])).

tff(c_785,plain,(
    ! [A_118,B_119] : k3_subset_1(A_118,k4_xboole_0(A_118,B_119)) = k3_xboole_0(A_118,B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_768])).

tff(c_794,plain,(
    ! [A_118,B_119] :
      ( k3_subset_1(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119)
      | ~ r1_tarski(k4_xboole_0(A_118,B_119),A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_447])).

tff(c_819,plain,(
    ! [A_118,B_119] : k3_subset_1(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_794])).

tff(c_129,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [A_73,B_74] : r1_tarski(k3_xboole_0(A_73,B_74),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_10])).

tff(c_776,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k3_subset_1(A_73,k3_xboole_0(A_73,B_74)) ),
    inference(resolution,[status(thm)],[c_138,c_747])).

tff(c_1470,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_776])).

tff(c_141,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_1529,plain,(
    ! [A_168,B_169] : k3_xboole_0(A_168,k4_xboole_0(A_168,B_169)) = k4_xboole_0(A_168,B_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_141])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_908,plain,(
    ! [A_128,B_129] : k3_subset_1(A_128,k3_xboole_0(A_128,B_129)) = k4_xboole_0(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_794])).

tff(c_938,plain,(
    ! [A_1,B_2] : k3_subset_1(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_908])).

tff(c_1550,plain,(
    ! [A_168,B_169] : k3_subset_1(k4_xboole_0(A_168,B_169),k4_xboole_0(A_168,B_169)) = k4_xboole_0(k4_xboole_0(A_168,B_169),A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_938])).

tff(c_1606,plain,(
    ! [A_168,B_169] : k4_xboole_0(k4_xboole_0(A_168,B_169),A_168) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_1550])).

tff(c_2101,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2081,c_1606])).

tff(c_2144,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2101,c_782])).

tff(c_2158,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_2144])).

tff(c_1622,plain,(
    ! [A_170,B_171] : k4_xboole_0(k4_xboole_0(A_170,B_171),A_170) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_1550])).

tff(c_1728,plain,(
    ! [A_172,B_173] : k4_xboole_0(k3_xboole_0(A_172,B_173),A_172) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1622])).

tff(c_1795,plain,(
    ! [B_174,A_175] : k4_xboole_0(k3_xboole_0(B_174,A_175),A_175) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1728])).

tff(c_1809,plain,(
    ! [B_174,A_175] : k3_xboole_0(k3_xboole_0(B_174,A_175),A_175) = k3_subset_1(k3_xboole_0(B_174,A_175),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1795,c_782])).

tff(c_4330,plain,(
    ! [B_211,A_212] : k3_xboole_0(k3_xboole_0(B_211,A_212),A_212) = k3_xboole_0(B_211,A_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_1809])).

tff(c_4479,plain,(
    ! [B_2,B_211] : k3_xboole_0(B_2,k3_xboole_0(B_211,B_2)) = k3_xboole_0(B_211,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4330])).

tff(c_18615,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18487,c_4479])).

tff(c_18713,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18487,c_2158,c_18615])).

tff(c_18715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5699,c_18713])).

tff(c_18716,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18717,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_46,plain,(
    ! [B_50,D_56,C_54,A_42] :
      ( k1_tops_1(B_50,D_56) = D_56
      | ~ v3_pre_topc(D_56,B_50)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(u1_struct_0(B_50)))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(B_50)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22925,plain,(
    ! [C_515,A_516] :
      ( ~ m1_subset_1(C_515,k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_22942,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_22925])).

tff(c_22953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_22942])).

tff(c_23064,plain,(
    ! [B_521,D_522] :
      ( k1_tops_1(B_521,D_522) = D_522
      | ~ v3_pre_topc(D_522,B_521)
      | ~ m1_subset_1(D_522,k1_zfmisc_1(u1_struct_0(B_521)))
      | ~ l1_pre_topc(B_521) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_23082,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_23064])).

tff(c_23093,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18717,c_23082])).

tff(c_19716,plain,(
    ! [A_441,B_442,C_443] :
      ( k7_subset_1(A_441,B_442,C_443) = k4_xboole_0(B_442,C_443)
      | ~ m1_subset_1(B_442,k1_zfmisc_1(A_441)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19730,plain,(
    ! [C_443] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_443) = k4_xboole_0('#skF_2',C_443) ),
    inference(resolution,[status(thm)],[c_50,c_19716])).

tff(c_21931,plain,(
    ! [A_501,B_502] :
      ( k7_subset_1(u1_struct_0(A_501),B_502,k2_tops_1(A_501,B_502)) = k1_tops_1(A_501,B_502)
      | ~ m1_subset_1(B_502,k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ l1_pre_topc(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_21944,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_21931])).

tff(c_21955,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_19730,c_21944])).

tff(c_18724,plain,(
    ! [B_381,A_382] :
      ( B_381 = A_382
      | ~ r1_tarski(B_381,A_382)
      | ~ r1_tarski(A_382,B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18735,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_18724])).

tff(c_21979,plain,
    ( k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21955,c_18735])).

tff(c_21993,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21955,c_21979])).

tff(c_22923,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_21993])).

tff(c_23096,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23093,c_22923])).

tff(c_23106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_23096])).

tff(c_23107,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_21993])).

tff(c_23123,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23107,c_42])).

tff(c_23127,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_23123])).

tff(c_23129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18716,c_23127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.21/4.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.21/4.10  
% 10.21/4.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.27/4.11  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.27/4.11  
% 10.27/4.11  %Foreground sorts:
% 10.27/4.11  
% 10.27/4.11  
% 10.27/4.11  %Background operators:
% 10.27/4.11  
% 10.27/4.11  
% 10.27/4.11  %Foreground operators:
% 10.27/4.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.27/4.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.27/4.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.27/4.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.27/4.11  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.27/4.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.27/4.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.27/4.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.27/4.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.27/4.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.27/4.11  tff('#skF_2', type, '#skF_2': $i).
% 10.27/4.11  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.27/4.11  tff('#skF_1', type, '#skF_1': $i).
% 10.27/4.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.27/4.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.27/4.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.27/4.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.27/4.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.27/4.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.27/4.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.27/4.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.27/4.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.27/4.11  
% 10.38/4.13  tff(f_146, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 10.38/4.13  tff(f_127, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 10.38/4.13  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.38/4.13  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.38/4.13  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.38/4.13  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.38/4.13  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.38/4.13  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.38/4.13  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.38/4.13  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.38/4.13  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.38/4.13  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.38/4.13  tff(f_68, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.38/4.13  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 10.38/4.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.38/4.13  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.38/4.13  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.38/4.13  tff(c_122, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 10.38/4.13  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.38/4.13  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.38/4.13  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.38/4.13  tff(c_44, plain, (![C_54, A_42, D_56, B_50]: (v3_pre_topc(C_54, A_42) | k1_tops_1(A_42, C_54)!=C_54 | ~m1_subset_1(D_56, k1_zfmisc_1(u1_struct_0(B_50))) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(B_50) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.38/4.13  tff(c_5497, plain, (![D_221, B_222]: (~m1_subset_1(D_221, k1_zfmisc_1(u1_struct_0(B_222))) | ~l1_pre_topc(B_222))), inference(splitLeft, [status(thm)], [c_44])).
% 10.38/4.13  tff(c_5511, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_5497])).
% 10.38/4.13  tff(c_5521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_5511])).
% 10.38/4.13  tff(c_5669, plain, (![C_225, A_226]: (v3_pre_topc(C_225, A_226) | k1_tops_1(A_226, C_225)!=C_225 | ~m1_subset_1(C_225, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226))), inference(splitRight, [status(thm)], [c_44])).
% 10.38/4.13  tff(c_5687, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_5669])).
% 10.38/4.13  tff(c_5698, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5687])).
% 10.38/4.13  tff(c_5699, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_122, c_5698])).
% 10.38/4.13  tff(c_1174, plain, (![B_146, A_147]: (r1_tarski(B_146, k2_pre_topc(A_147, B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.38/4.13  tff(c_1185, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1174])).
% 10.38/4.13  tff(c_1194, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1185])).
% 10.38/4.13  tff(c_1443, plain, (![A_164, B_165]: (m1_subset_1(k2_pre_topc(A_164, B_165), k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.38/4.13  tff(c_22, plain, (![A_16, B_17, C_18]: (k7_subset_1(A_16, B_17, C_18)=k4_xboole_0(B_17, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.38/4.13  tff(c_17129, plain, (![A_362, B_363, C_364]: (k7_subset_1(u1_struct_0(A_362), k2_pre_topc(A_362, B_363), C_364)=k4_xboole_0(k2_pre_topc(A_362, B_363), C_364) | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0(A_362))) | ~l1_pre_topc(A_362))), inference(resolution, [status(thm)], [c_1443, c_22])).
% 10.38/4.13  tff(c_17142, plain, (![C_364]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_364)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_364) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_17129])).
% 10.38/4.13  tff(c_17380, plain, (![C_367]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_367)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_367))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_17142])).
% 10.38/4.13  tff(c_62, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.38/4.13  tff(c_224, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_122, c_62])).
% 10.38/4.13  tff(c_17401, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17380, c_224])).
% 10.38/4.13  tff(c_32, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.38/4.13  tff(c_629, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.38/4.13  tff(c_643, plain, (![B_28, A_27]: (k4_xboole_0(B_28, A_27)=k3_subset_1(B_28, A_27) | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_32, c_629])).
% 10.38/4.13  tff(c_1202, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1194, c_643])).
% 10.38/4.13  tff(c_17480, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17401, c_1202])).
% 10.38/4.13  tff(c_440, plain, (![A_95, B_96]: (k3_subset_1(A_95, k3_subset_1(A_95, B_96))=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.38/4.13  tff(c_447, plain, (![B_28, A_27]: (k3_subset_1(B_28, k3_subset_1(B_28, A_27))=A_27 | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_32, c_440])).
% 10.38/4.13  tff(c_17547, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17480, c_447])).
% 10.38/4.13  tff(c_17558, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_17547])).
% 10.38/4.13  tff(c_42, plain, (![A_39, B_41]: (k7_subset_1(u1_struct_0(A_39), k2_pre_topc(A_39, B_41), k1_tops_1(A_39, B_41))=k2_tops_1(A_39, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.38/4.13  tff(c_17398, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17380, c_42])).
% 10.38/4.13  tff(c_17425, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_17398])).
% 10.38/4.13  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.38/4.13  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.38/4.13  tff(c_747, plain, (![B_116, A_117]: (k4_xboole_0(B_116, A_117)=k3_subset_1(B_116, A_117) | ~r1_tarski(A_117, B_116))), inference(resolution, [status(thm)], [c_32, c_629])).
% 10.38/4.13  tff(c_768, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_747])).
% 10.38/4.13  tff(c_782, plain, (![A_5, B_6]: (k3_subset_1(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_768])).
% 10.38/4.13  tff(c_18468, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17425, c_782])).
% 10.38/4.13  tff(c_18487, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17558, c_18468])).
% 10.38/4.13  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.38/4.13  tff(c_28, plain, (![A_26]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.38/4.13  tff(c_641, plain, (![A_26]: (k4_xboole_0(A_26, k1_xboole_0)=k3_subset_1(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_629])).
% 10.38/4.13  tff(c_646, plain, (![A_26]: (k3_subset_1(A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_641])).
% 10.38/4.13  tff(c_1027, plain, (![A_132, B_133, C_134]: (k7_subset_1(A_132, B_133, C_134)=k4_xboole_0(B_133, C_134) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.38/4.13  tff(c_1041, plain, (![C_134]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_134)=k4_xboole_0('#skF_2', C_134))), inference(resolution, [status(thm)], [c_50, c_1027])).
% 10.38/4.13  tff(c_2057, plain, (![A_180, B_181]: (k7_subset_1(u1_struct_0(A_180), B_181, k2_tops_1(A_180, B_181))=k1_tops_1(A_180, B_181) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.38/4.13  tff(c_2070, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2057])).
% 10.38/4.13  tff(c_2081, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1041, c_2070])).
% 10.38/4.13  tff(c_449, plain, (![A_26]: (k3_subset_1(A_26, k3_subset_1(A_26, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_440])).
% 10.38/4.13  tff(c_648, plain, (![A_26]: (k3_subset_1(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_646, c_449])).
% 10.38/4.13  tff(c_785, plain, (![A_118, B_119]: (k3_subset_1(A_118, k4_xboole_0(A_118, B_119))=k3_xboole_0(A_118, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_768])).
% 10.38/4.13  tff(c_794, plain, (![A_118, B_119]: (k3_subset_1(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119) | ~r1_tarski(k4_xboole_0(A_118, B_119), A_118))), inference(superposition, [status(thm), theory('equality')], [c_785, c_447])).
% 10.38/4.13  tff(c_819, plain, (![A_118, B_119]: (k3_subset_1(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_794])).
% 10.38/4.13  tff(c_129, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.38/4.13  tff(c_138, plain, (![A_73, B_74]: (r1_tarski(k3_xboole_0(A_73, B_74), A_73))), inference(superposition, [status(thm), theory('equality')], [c_129, c_10])).
% 10.38/4.13  tff(c_776, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k3_subset_1(A_73, k3_xboole_0(A_73, B_74)))), inference(resolution, [status(thm)], [c_138, c_747])).
% 10.38/4.13  tff(c_1470, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_819, c_776])).
% 10.38/4.13  tff(c_141, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k3_xboole_0(A_8, k4_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_129])).
% 10.38/4.13  tff(c_1529, plain, (![A_168, B_169]: (k3_xboole_0(A_168, k4_xboole_0(A_168, B_169))=k4_xboole_0(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_141])).
% 10.38/4.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.38/4.13  tff(c_908, plain, (![A_128, B_129]: (k3_subset_1(A_128, k3_xboole_0(A_128, B_129))=k4_xboole_0(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_794])).
% 10.38/4.13  tff(c_938, plain, (![A_1, B_2]: (k3_subset_1(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_908])).
% 10.38/4.13  tff(c_1550, plain, (![A_168, B_169]: (k3_subset_1(k4_xboole_0(A_168, B_169), k4_xboole_0(A_168, B_169))=k4_xboole_0(k4_xboole_0(A_168, B_169), A_168))), inference(superposition, [status(thm), theory('equality')], [c_1529, c_938])).
% 10.38/4.13  tff(c_1606, plain, (![A_168, B_169]: (k4_xboole_0(k4_xboole_0(A_168, B_169), A_168)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_648, c_1550])).
% 10.38/4.13  tff(c_2101, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2081, c_1606])).
% 10.38/4.13  tff(c_2144, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2101, c_782])).
% 10.38/4.13  tff(c_2158, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_2144])).
% 10.38/4.13  tff(c_1622, plain, (![A_170, B_171]: (k4_xboole_0(k4_xboole_0(A_170, B_171), A_170)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_648, c_1550])).
% 10.38/4.13  tff(c_1728, plain, (![A_172, B_173]: (k4_xboole_0(k3_xboole_0(A_172, B_173), A_172)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1622])).
% 10.38/4.13  tff(c_1795, plain, (![B_174, A_175]: (k4_xboole_0(k3_xboole_0(B_174, A_175), A_175)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1728])).
% 10.38/4.13  tff(c_1809, plain, (![B_174, A_175]: (k3_xboole_0(k3_xboole_0(B_174, A_175), A_175)=k3_subset_1(k3_xboole_0(B_174, A_175), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1795, c_782])).
% 10.38/4.13  tff(c_4330, plain, (![B_211, A_212]: (k3_xboole_0(k3_xboole_0(B_211, A_212), A_212)=k3_xboole_0(B_211, A_212))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_1809])).
% 10.38/4.13  tff(c_4479, plain, (![B_2, B_211]: (k3_xboole_0(B_2, k3_xboole_0(B_211, B_2))=k3_xboole_0(B_211, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4330])).
% 10.38/4.13  tff(c_18615, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18487, c_4479])).
% 10.38/4.13  tff(c_18713, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18487, c_2158, c_18615])).
% 10.38/4.13  tff(c_18715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5699, c_18713])).
% 10.38/4.13  tff(c_18716, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 10.38/4.13  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.38/4.13  tff(c_18717, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 10.38/4.13  tff(c_46, plain, (![B_50, D_56, C_54, A_42]: (k1_tops_1(B_50, D_56)=D_56 | ~v3_pre_topc(D_56, B_50) | ~m1_subset_1(D_56, k1_zfmisc_1(u1_struct_0(B_50))) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(B_50) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.38/4.13  tff(c_22925, plain, (![C_515, A_516]: (~m1_subset_1(C_515, k1_zfmisc_1(u1_struct_0(A_516))) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516))), inference(splitLeft, [status(thm)], [c_46])).
% 10.38/4.13  tff(c_22942, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_22925])).
% 10.38/4.13  tff(c_22953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_22942])).
% 10.38/4.13  tff(c_23064, plain, (![B_521, D_522]: (k1_tops_1(B_521, D_522)=D_522 | ~v3_pre_topc(D_522, B_521) | ~m1_subset_1(D_522, k1_zfmisc_1(u1_struct_0(B_521))) | ~l1_pre_topc(B_521))), inference(splitRight, [status(thm)], [c_46])).
% 10.38/4.13  tff(c_23082, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_23064])).
% 10.38/4.13  tff(c_23093, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18717, c_23082])).
% 10.38/4.13  tff(c_19716, plain, (![A_441, B_442, C_443]: (k7_subset_1(A_441, B_442, C_443)=k4_xboole_0(B_442, C_443) | ~m1_subset_1(B_442, k1_zfmisc_1(A_441)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.38/4.13  tff(c_19730, plain, (![C_443]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_443)=k4_xboole_0('#skF_2', C_443))), inference(resolution, [status(thm)], [c_50, c_19716])).
% 10.38/4.13  tff(c_21931, plain, (![A_501, B_502]: (k7_subset_1(u1_struct_0(A_501), B_502, k2_tops_1(A_501, B_502))=k1_tops_1(A_501, B_502) | ~m1_subset_1(B_502, k1_zfmisc_1(u1_struct_0(A_501))) | ~l1_pre_topc(A_501))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.38/4.13  tff(c_21944, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_21931])).
% 10.38/4.13  tff(c_21955, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_19730, c_21944])).
% 10.38/4.13  tff(c_18724, plain, (![B_381, A_382]: (B_381=A_382 | ~r1_tarski(B_381, A_382) | ~r1_tarski(A_382, B_381))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.38/4.13  tff(c_18735, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_18724])).
% 10.38/4.13  tff(c_21979, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_21955, c_18735])).
% 10.38/4.13  tff(c_21993, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_21955, c_21979])).
% 10.38/4.13  tff(c_22923, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_21993])).
% 10.38/4.13  tff(c_23096, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23093, c_22923])).
% 10.38/4.13  tff(c_23106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_23096])).
% 10.38/4.13  tff(c_23107, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_21993])).
% 10.38/4.13  tff(c_23123, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23107, c_42])).
% 10.38/4.13  tff(c_23127, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_23123])).
% 10.38/4.13  tff(c_23129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18716, c_23127])).
% 10.38/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/4.13  
% 10.38/4.13  Inference rules
% 10.38/4.13  ----------------------
% 10.38/4.13  #Ref     : 0
% 10.38/4.13  #Sup     : 5781
% 10.38/4.13  #Fact    : 0
% 10.38/4.13  #Define  : 0
% 10.38/4.13  #Split   : 14
% 10.38/4.13  #Chain   : 0
% 10.38/4.13  #Close   : 0
% 10.38/4.13  
% 10.38/4.13  Ordering : KBO
% 10.38/4.13  
% 10.38/4.13  Simplification rules
% 10.38/4.13  ----------------------
% 10.38/4.13  #Subsume      : 461
% 10.38/4.13  #Demod        : 6741
% 10.38/4.13  #Tautology    : 3810
% 10.38/4.13  #SimpNegUnit  : 11
% 10.38/4.13  #BackRed      : 25
% 10.38/4.13  
% 10.38/4.13  #Partial instantiations: 0
% 10.38/4.13  #Strategies tried      : 1
% 10.38/4.13  
% 10.38/4.13  Timing (in seconds)
% 10.38/4.13  ----------------------
% 10.38/4.13  Preprocessing        : 0.37
% 10.38/4.13  Parsing              : 0.20
% 10.38/4.13  CNF conversion       : 0.02
% 10.38/4.13  Main loop            : 2.90
% 10.38/4.13  Inferencing          : 0.64
% 10.38/4.13  Reduction            : 1.58
% 10.38/4.13  Demodulation         : 1.36
% 10.38/4.13  BG Simplification    : 0.07
% 10.38/4.13  Subsumption          : 0.47
% 10.38/4.13  Abstraction          : 0.12
% 10.38/4.13  MUC search           : 0.00
% 10.38/4.14  Cooper               : 0.00
% 10.38/4.14  Total                : 3.32
% 10.38/4.14  Index Insertion      : 0.00
% 10.38/4.14  Index Deletion       : 0.00
% 10.38/4.14  Index Matching       : 0.00
% 10.38/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
