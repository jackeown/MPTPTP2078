%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:46 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 154 expanded)
%              Number of leaves         :   37 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 406 expanded)
%              Number of equality atoms :   37 (  70 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
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

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_74,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1299,plain,(
    ! [B_114,A_115] :
      ( v2_tops_1(B_114,A_115)
      | k1_tops_1(A_115,B_114) != k1_xboole_0
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1319,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1299])).

tff(c_1333,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1319])).

tff(c_1334,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1333])).

tff(c_867,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(k1_tops_1(A_100,B_101),B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_875,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_867])).

tff(c_880,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_875])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1115,plain,(
    ! [A_110,B_111] :
      ( v3_pre_topc(k1_tops_1(A_110,B_111),A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1125,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1115])).

tff(c_1133,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1125])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_887,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_880,c_12])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_215,plain,(
    ! [B_64,A_65] : k1_setfam_1(k2_tarski(B_64,A_65)) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_200])).

tff(c_24,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_221,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_24])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_563,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_subset_1(A_84,B_85,C_86) = k4_xboole_0(B_85,C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1000,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_105) = k4_xboole_0('#skF_2',C_105) ),
    inference(resolution,[status(thm)],[c_40,c_563])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1006,plain,(
    ! [C_105] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_105),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_20])).

tff(c_1014,plain,(
    ! [C_106] : m1_subset_1(k4_xboole_0('#skF_2',C_106),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1006])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1038,plain,(
    ! [C_107] : r1_tarski(k4_xboole_0('#skF_2',C_107),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1014,c_26])).

tff(c_1053,plain,(
    ! [B_108] : r1_tarski(k3_xboole_0('#skF_2',B_108),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1038])).

tff(c_1062,plain,(
    ! [B_64] : r1_tarski(k3_xboole_0(B_64,'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_1053])).

tff(c_1835,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_1062])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [C_46] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_46
      | ~ v3_pre_topc(C_46,'#skF_1')
      | ~ r1_tarski(C_46,'#skF_2')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_891,plain,(
    ! [C_102] :
      ( k1_xboole_0 = C_102
      | ~ v3_pre_topc(C_102,'#skF_1')
      | ~ r1_tarski(C_102,'#skF_2')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64])).

tff(c_904,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v3_pre_topc(A_22,'#skF_1')
      | ~ r1_tarski(A_22,'#skF_2')
      | ~ r1_tarski(A_22,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_891])).

tff(c_1872,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1835,c_904])).

tff(c_1880,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_1133,c_1872])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1334,c_1880])).

tff(c_1883,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1884,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1893,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_48])).

tff(c_50,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1891,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_50])).

tff(c_52,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1895,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_52])).

tff(c_2881,plain,(
    ! [A_188,B_189] :
      ( k1_tops_1(A_188,B_189) = k1_xboole_0
      | ~ v2_tops_1(B_189,A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2901,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2881])).

tff(c_2916,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1884,c_2901])).

tff(c_3186,plain,(
    ! [B_197,A_198,C_199] :
      ( r1_tarski(B_197,k1_tops_1(A_198,C_199))
      | ~ r1_tarski(B_197,C_199)
      | ~ v3_pre_topc(B_197,A_198)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3206,plain,(
    ! [B_197] :
      ( r1_tarski(B_197,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_197,'#skF_2')
      | ~ v3_pre_topc(B_197,'#skF_1')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_3186])).

tff(c_3379,plain,(
    ! [B_203] :
      ( r1_tarski(B_203,k1_xboole_0)
      | ~ r1_tarski(B_203,'#skF_2')
      | ~ v3_pre_topc(B_203,'#skF_1')
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2916,c_3206])).

tff(c_3411,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1895,c_3379])).

tff(c_3432,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_1891,c_3411])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1885,plain,(
    ! [A_134,B_135] : r1_tarski(k3_xboole_0(A_134,B_135),A_134) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1888,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1885])).

tff(c_2212,plain,(
    ! [B_157,A_158] :
      ( B_157 = A_158
      | ~ r1_tarski(B_157,A_158)
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2231,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1888,c_2212])).

tff(c_3438,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3432,c_2231])).

tff(c_3447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1883,c_3438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  
% 4.51/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.79  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.51/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.51/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.51/1.79  
% 4.61/1.81  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.61/1.81  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.61/1.81  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.61/1.81  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.61/1.81  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.61/1.81  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.61/1.81  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.61/1.81  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.61/1.81  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.61/1.81  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.61/1.81  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.61/1.81  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.61/1.81  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.61/1.81  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.61/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.61/1.81  tff(c_46, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_74, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.61/1.81  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_1299, plain, (![B_114, A_115]: (v2_tops_1(B_114, A_115) | k1_tops_1(A_115, B_114)!=k1_xboole_0 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.61/1.81  tff(c_1319, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1299])).
% 4.61/1.81  tff(c_1333, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1319])).
% 4.61/1.81  tff(c_1334, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_1333])).
% 4.61/1.81  tff(c_867, plain, (![A_100, B_101]: (r1_tarski(k1_tops_1(A_100, B_101), B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.61/1.81  tff(c_875, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_867])).
% 4.61/1.81  tff(c_880, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_875])).
% 4.61/1.81  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_1115, plain, (![A_110, B_111]: (v3_pre_topc(k1_tops_1(A_110, B_111), A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.61/1.81  tff(c_1125, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1115])).
% 4.61/1.81  tff(c_1133, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1125])).
% 4.61/1.81  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.61/1.81  tff(c_887, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_880, c_12])).
% 4.61/1.81  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.61/1.81  tff(c_200, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.61/1.81  tff(c_215, plain, (![B_64, A_65]: (k1_setfam_1(k2_tarski(B_64, A_65))=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_18, c_200])).
% 4.61/1.81  tff(c_24, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.61/1.81  tff(c_221, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_215, c_24])).
% 4.61/1.81  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.61/1.81  tff(c_563, plain, (![A_84, B_85, C_86]: (k7_subset_1(A_84, B_85, C_86)=k4_xboole_0(B_85, C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.61/1.81  tff(c_1000, plain, (![C_105]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_105)=k4_xboole_0('#skF_2', C_105))), inference(resolution, [status(thm)], [c_40, c_563])).
% 4.61/1.81  tff(c_20, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.81  tff(c_1006, plain, (![C_105]: (m1_subset_1(k4_xboole_0('#skF_2', C_105), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_20])).
% 4.61/1.81  tff(c_1014, plain, (![C_106]: (m1_subset_1(k4_xboole_0('#skF_2', C_106), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1006])).
% 4.61/1.81  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.61/1.81  tff(c_1038, plain, (![C_107]: (r1_tarski(k4_xboole_0('#skF_2', C_107), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1014, c_26])).
% 4.61/1.81  tff(c_1053, plain, (![B_108]: (r1_tarski(k3_xboole_0('#skF_2', B_108), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1038])).
% 4.61/1.81  tff(c_1062, plain, (![B_64]: (r1_tarski(k3_xboole_0(B_64, '#skF_2'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_221, c_1053])).
% 4.61/1.81  tff(c_1835, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_887, c_1062])).
% 4.61/1.81  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.61/1.81  tff(c_64, plain, (![C_46]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_46 | ~v3_pre_topc(C_46, '#skF_1') | ~r1_tarski(C_46, '#skF_2') | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_891, plain, (![C_102]: (k1_xboole_0=C_102 | ~v3_pre_topc(C_102, '#skF_1') | ~r1_tarski(C_102, '#skF_2') | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_64])).
% 4.61/1.81  tff(c_904, plain, (![A_22]: (k1_xboole_0=A_22 | ~v3_pre_topc(A_22, '#skF_1') | ~r1_tarski(A_22, '#skF_2') | ~r1_tarski(A_22, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_891])).
% 4.61/1.81  tff(c_1872, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1835, c_904])).
% 4.61/1.81  tff(c_1880, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_880, c_1133, c_1872])).
% 4.61/1.81  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1334, c_1880])).
% 4.61/1.81  tff(c_1883, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 4.61/1.81  tff(c_1884, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.61/1.81  tff(c_48, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_1893, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_48])).
% 4.61/1.81  tff(c_50, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_1891, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_50])).
% 4.61/1.81  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.61/1.81  tff(c_1895, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_52])).
% 4.61/1.81  tff(c_2881, plain, (![A_188, B_189]: (k1_tops_1(A_188, B_189)=k1_xboole_0 | ~v2_tops_1(B_189, A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.61/1.81  tff(c_2901, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2881])).
% 4.61/1.81  tff(c_2916, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1884, c_2901])).
% 4.61/1.81  tff(c_3186, plain, (![B_197, A_198, C_199]: (r1_tarski(B_197, k1_tops_1(A_198, C_199)) | ~r1_tarski(B_197, C_199) | ~v3_pre_topc(B_197, A_198) | ~m1_subset_1(C_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.81  tff(c_3206, plain, (![B_197]: (r1_tarski(B_197, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_197, '#skF_2') | ~v3_pre_topc(B_197, '#skF_1') | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_3186])).
% 4.61/1.81  tff(c_3379, plain, (![B_203]: (r1_tarski(B_203, k1_xboole_0) | ~r1_tarski(B_203, '#skF_2') | ~v3_pre_topc(B_203, '#skF_1') | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2916, c_3206])).
% 4.61/1.81  tff(c_3411, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1895, c_3379])).
% 4.61/1.81  tff(c_3432, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1893, c_1891, c_3411])).
% 4.61/1.81  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.61/1.81  tff(c_1885, plain, (![A_134, B_135]: (r1_tarski(k3_xboole_0(A_134, B_135), A_134))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.61/1.81  tff(c_1888, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1885])).
% 4.61/1.81  tff(c_2212, plain, (![B_157, A_158]: (B_157=A_158 | ~r1_tarski(B_157, A_158) | ~r1_tarski(A_158, B_157))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.81  tff(c_2231, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_1888, c_2212])).
% 4.61/1.81  tff(c_3438, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3432, c_2231])).
% 4.61/1.81  tff(c_3447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1883, c_3438])).
% 4.61/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.81  
% 4.61/1.81  Inference rules
% 4.61/1.81  ----------------------
% 4.61/1.81  #Ref     : 0
% 4.61/1.81  #Sup     : 790
% 4.61/1.81  #Fact    : 0
% 4.61/1.81  #Define  : 0
% 4.61/1.81  #Split   : 16
% 4.61/1.81  #Chain   : 0
% 4.61/1.81  #Close   : 0
% 4.61/1.81  
% 4.61/1.81  Ordering : KBO
% 4.61/1.81  
% 4.61/1.81  Simplification rules
% 4.61/1.81  ----------------------
% 4.61/1.81  #Subsume      : 21
% 4.61/1.81  #Demod        : 561
% 4.61/1.81  #Tautology    : 440
% 4.61/1.81  #SimpNegUnit  : 12
% 4.61/1.81  #BackRed      : 8
% 4.61/1.81  
% 4.61/1.81  #Partial instantiations: 0
% 4.61/1.81  #Strategies tried      : 1
% 4.61/1.81  
% 4.61/1.81  Timing (in seconds)
% 4.61/1.81  ----------------------
% 4.61/1.81  Preprocessing        : 0.34
% 4.61/1.81  Parsing              : 0.18
% 4.61/1.81  CNF conversion       : 0.02
% 4.61/1.81  Main loop            : 0.70
% 4.61/1.81  Inferencing          : 0.22
% 4.61/1.81  Reduction            : 0.28
% 4.61/1.81  Demodulation         : 0.22
% 4.61/1.81  BG Simplification    : 0.03
% 4.61/1.82  Subsumption          : 0.11
% 4.61/1.82  Abstraction          : 0.03
% 4.61/1.82  MUC search           : 0.00
% 4.61/1.82  Cooper               : 0.00
% 4.61/1.82  Total                : 1.08
% 4.61/1.82  Index Insertion      : 0.00
% 4.61/1.82  Index Deletion       : 0.00
% 4.61/1.82  Index Matching       : 0.00
% 4.61/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
