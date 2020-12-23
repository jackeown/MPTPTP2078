%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 27.79s
% Output     : CNFRefutation 27.91s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 834 expanded)
%              Number of leaves         :   36 ( 292 expanded)
%              Depth                    :   19
%              Number of atoms          :  229 (1802 expanded)
%              Number of equality atoms :   65 ( 453 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_121,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_82,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_pre_topc(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_127,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_54])).

tff(c_341,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k7_subset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_379,plain,(
    ! [A_101,B_102,C_103] :
      ( r1_tarski(k7_subset_1(A_101,B_102,C_103),A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(resolution,[status(thm)],[c_341,c_22])).

tff(c_385,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_379])).

tff(c_515,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_934,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_515])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_934])).

tff(c_943,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_354,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_341])).

tff(c_1985,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_354])).

tff(c_36,plain,(
    ! [C_50,A_38,D_52,B_46] :
      ( v3_pre_topc(C_50,A_38)
      | k1_tops_1(A_38,C_50) != C_50
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(B_46)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2089,plain,(
    ! [D_187,B_188] :
      ( ~ m1_subset_1(D_187,k1_zfmisc_1(u1_struct_0(B_188)))
      | ~ l1_pre_topc(B_188) ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_2092,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1985,c_2089])).

tff(c_2150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2092])).

tff(c_2186,plain,(
    ! [C_195,A_196] :
      ( v3_pre_topc(C_195,A_196)
      | k1_tops_1(A_196,C_195) != C_195
      | ~ m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2245,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2186])).

tff(c_2286,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2245])).

tff(c_2287,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2286])).

tff(c_387,plain,(
    ! [A_104,B_105,C_106] :
      ( k7_subset_1(A_104,B_105,C_106) = k4_xboole_0(B_105,C_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_403,plain,(
    ! [C_106] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_106) = k4_xboole_0('#skF_2',C_106) ),
    inference(resolution,[status(thm)],[c_42,c_387])).

tff(c_1395,plain,(
    ! [A_156,B_157] :
      ( k7_subset_1(u1_struct_0(A_156),B_157,k2_tops_1(A_156,B_157)) = k1_tops_1(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1429,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1395])).

tff(c_1456,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_403,c_1429])).

tff(c_478,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(B_113,k2_pre_topc(A_114,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_489,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_478])).

tff(c_501,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_489])).

tff(c_1193,plain,(
    ! [A_151,B_152] :
      ( m1_subset_1(k2_pre_topc(A_151,B_152),k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( k7_subset_1(A_15,B_16,C_17) = k4_xboole_0(B_16,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12542,plain,(
    ! [A_434,B_435,C_436] :
      ( k7_subset_1(u1_struct_0(A_434),k2_pre_topc(A_434,B_435),C_436) = k4_xboole_0(k2_pre_topc(A_434,B_435),C_436)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434) ) ),
    inference(resolution,[status(thm)],[c_1193,c_16])).

tff(c_12650,plain,(
    ! [C_436] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_436) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_436)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_12542])).

tff(c_13004,plain,(
    ! [C_441] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_441) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_441) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12650])).

tff(c_13033,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13004,c_127])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_136,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [B_24,A_23] :
      ( k4_xboole_0(B_24,A_23) = k3_subset_1(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_508,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_501,c_149])).

tff(c_13132,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13033,c_508])).

tff(c_153,plain,(
    ! [A_84,B_85] :
      ( k3_subset_1(A_84,k3_subset_1(A_84,B_85)) = B_85
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_153])).

tff(c_13196,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13132,c_162])).

tff(c_13202,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_13196])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_1039,plain,(
    ! [A_141,C_142] : k7_subset_1(A_141,A_141,C_142) = k4_xboole_0(A_141,C_142) ),
    inference(resolution,[status(thm)],[c_55,c_387])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k7_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1052,plain,(
    ! [A_141,C_142] :
      ( m1_subset_1(k4_xboole_0(A_141,C_142),k1_zfmisc_1(A_141))
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_10])).

tff(c_1065,plain,(
    ! [A_141,C_142] : m1_subset_1(k4_xboole_0(A_141,C_142),k1_zfmisc_1(A_141)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1052])).

tff(c_2298,plain,(
    m1_subset_1(k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_1065])).

tff(c_13178,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13132,c_2298])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13332,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13202,c_8])).

tff(c_13345,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13178,c_13332])).

tff(c_311,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k3_subset_1(A_94,B_95),k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k3_subset_1(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_335,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,k3_subset_1(A_94,B_95)) = k3_subset_1(A_94,k3_subset_1(A_94,B_95))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_13358,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_13345,c_335])).

tff(c_13386,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13202,c_13132,c_13132,c_13358])).

tff(c_404,plain,(
    ! [A_4,C_106] : k7_subset_1(A_4,A_4,C_106) = k4_xboole_0(A_4,C_106) ),
    inference(resolution,[status(thm)],[c_55,c_387])).

tff(c_10964,plain,(
    ! [A_402,B_403,C_404,C_405] :
      ( k7_subset_1(A_402,k7_subset_1(A_402,B_403,C_404),C_405) = k4_xboole_0(k7_subset_1(A_402,B_403,C_404),C_405)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(A_402)) ) ),
    inference(resolution,[status(thm)],[c_10,c_387])).

tff(c_11064,plain,(
    ! [A_4,C_404,C_405] : k7_subset_1(A_4,k7_subset_1(A_4,A_4,C_404),C_405) = k4_xboole_0(k7_subset_1(A_4,A_4,C_404),C_405) ),
    inference(resolution,[status(thm)],[c_55,c_10964])).

tff(c_20302,plain,(
    ! [A_558,C_559,C_560] : k7_subset_1(A_558,k4_xboole_0(A_558,C_559),C_560) = k4_xboole_0(k4_xboole_0(A_558,C_559),C_560) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_404,c_11064])).

tff(c_358,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_tarski(k7_subset_1(A_96,B_97,C_98),A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(resolution,[status(thm)],[c_341,c_22])).

tff(c_20353,plain,(
    ! [A_558,C_559,C_560] :
      ( r1_tarski(k4_xboole_0(k4_xboole_0(A_558,C_559),C_560),A_558)
      | ~ m1_subset_1(k4_xboole_0(A_558,C_559),k1_zfmisc_1(A_558)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20302,c_358])).

tff(c_20510,plain,(
    ! [A_561,C_562,C_563] : r1_tarski(k4_xboole_0(k4_xboole_0(A_561,C_562),C_563),A_561) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_20353])).

tff(c_20790,plain,(
    ! [C_566] : r1_tarski(k4_xboole_0('#skF_2',C_566),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13386,c_20510])).

tff(c_20825,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_20790])).

tff(c_34,plain,(
    ! [A_35,B_37] :
      ( k7_subset_1(u1_struct_0(A_35),k2_pre_topc(A_35,B_37),k1_tops_1(A_35,B_37)) = k2_tops_1(A_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_13024,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13004,c_34])).

tff(c_13058,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_13024])).

tff(c_20356,plain,(
    ! [A_558,C_559,C_560] :
      ( m1_subset_1(k4_xboole_0(k4_xboole_0(A_558,C_559),C_560),k1_zfmisc_1(A_558))
      | ~ m1_subset_1(k4_xboole_0(A_558,C_559),k1_zfmisc_1(A_558)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20302,c_10])).

tff(c_20873,plain,(
    ! [A_567,C_568,C_569] : m1_subset_1(k4_xboole_0(k4_xboole_0(A_567,C_568),C_569),k1_zfmisc_1(A_567)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_20356])).

tff(c_21451,plain,(
    ! [C_574] : m1_subset_1(k4_xboole_0('#skF_2',C_574),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13386,c_20873])).

tff(c_21509,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_21451])).

tff(c_21609,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_21509,c_4])).

tff(c_21626,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13058,c_21609])).

tff(c_66626,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21626,c_162])).

tff(c_66670,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20825,c_13202,c_66626])).

tff(c_66672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2287,c_66670])).

tff(c_66673,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_66674,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_66949,plain,(
    ! [A_1139,B_1140,C_1141] :
      ( k7_subset_1(A_1139,B_1140,C_1141) = k4_xboole_0(B_1140,C_1141)
      | ~ m1_subset_1(B_1140,k1_zfmisc_1(A_1139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66962,plain,(
    ! [C_1141] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1141) = k4_xboole_0('#skF_2',C_1141) ),
    inference(resolution,[status(thm)],[c_42,c_66949])).

tff(c_67574,plain,(
    ! [A_1175,B_1176] :
      ( k7_subset_1(u1_struct_0(A_1175),B_1176,k2_tops_1(A_1175,B_1176)) = k1_tops_1(A_1175,B_1176)
      | ~ m1_subset_1(B_1176,k1_zfmisc_1(u1_struct_0(A_1175)))
      | ~ l1_pre_topc(A_1175) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_67610,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_67574])).

tff(c_67640,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_66962,c_67610])).

tff(c_67038,plain,(
    ! [C_1151] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1151) = k4_xboole_0('#skF_2',C_1151) ),
    inference(resolution,[status(thm)],[c_42,c_66949])).

tff(c_67044,plain,(
    ! [C_1151] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_1151),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67038,c_10])).

tff(c_67050,plain,(
    ! [C_1151] : m1_subset_1(k4_xboole_0('#skF_2',C_1151),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67044])).

tff(c_67651,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_67640,c_67050])).

tff(c_38,plain,(
    ! [B_46,D_52,C_50,A_38] :
      ( k1_tops_1(B_46,D_52) = D_52
      | ~ v3_pre_topc(D_52,B_46)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(B_46)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_68119,plain,(
    ! [C_1209,A_1210] :
      ( ~ m1_subset_1(C_1209,k1_zfmisc_1(u1_struct_0(A_1210)))
      | ~ l1_pre_topc(A_1210)
      | ~ v2_pre_topc(A_1210) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_68122,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_67651,c_68119])).

tff(c_68177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_68122])).

tff(c_68379,plain,(
    ! [B_1223,D_1224] :
      ( k1_tops_1(B_1223,D_1224) = D_1224
      | ~ v3_pre_topc(D_1224,B_1223)
      | ~ m1_subset_1(D_1224,k1_zfmisc_1(u1_struct_0(B_1223)))
      | ~ l1_pre_topc(B_1223) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_68436,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_68379])).

tff(c_68472,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_66674,c_68436])).

tff(c_68495,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68472,c_34])).

tff(c_68499,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_68495])).

tff(c_68501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66673,c_68499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.79/18.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.91/18.71  
% 27.91/18.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.91/18.71  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 27.91/18.71  
% 27.91/18.71  %Foreground sorts:
% 27.91/18.71  
% 27.91/18.71  
% 27.91/18.71  %Background operators:
% 27.91/18.71  
% 27.91/18.71  
% 27.91/18.71  %Foreground operators:
% 27.91/18.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.91/18.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.91/18.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.91/18.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.91/18.71  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 27.91/18.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.91/18.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.91/18.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.91/18.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 27.91/18.71  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 27.91/18.71  tff('#skF_2', type, '#skF_2': $i).
% 27.91/18.71  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 27.91/18.71  tff('#skF_1', type, '#skF_1': $i).
% 27.91/18.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.91/18.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.91/18.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.91/18.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.91/18.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.91/18.71  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 27.91/18.71  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 27.91/18.71  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.91/18.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.91/18.71  
% 27.91/18.73  tff(f_140, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 27.91/18.73  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 27.91/18.73  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 27.91/18.73  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 27.91/18.73  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 27.91/18.73  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 27.91/18.73  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 27.91/18.73  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 27.91/18.73  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 27.91/18.73  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 27.91/18.73  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 27.91/18.73  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 27.91/18.73  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 27.91/18.73  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 27.91/18.73  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.91/18.73  tff(c_82, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 27.91/18.73  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.91/18.73  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.91/18.73  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.91/18.73  tff(c_28, plain, (![A_28, B_29]: (m1_subset_1(k2_pre_topc(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.91/18.73  tff(c_54, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 27.91/18.73  tff(c_127, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_82, c_54])).
% 27.91/18.73  tff(c_341, plain, (![A_96, B_97, C_98]: (m1_subset_1(k7_subset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.91/18.73  tff(c_22, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.91/18.73  tff(c_379, plain, (![A_101, B_102, C_103]: (r1_tarski(k7_subset_1(A_101, B_102, C_103), A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(resolution, [status(thm)], [c_341, c_22])).
% 27.91/18.73  tff(c_385, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_379])).
% 27.91/18.73  tff(c_515, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_385])).
% 27.91/18.73  tff(c_934, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_515])).
% 27.91/18.73  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_934])).
% 27.91/18.73  tff(c_943, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_385])).
% 27.91/18.73  tff(c_354, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_341])).
% 27.91/18.73  tff(c_1985, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_943, c_354])).
% 27.91/18.73  tff(c_36, plain, (![C_50, A_38, D_52, B_46]: (v3_pre_topc(C_50, A_38) | k1_tops_1(A_38, C_50)!=C_50 | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(B_46))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(B_46) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 27.91/18.73  tff(c_2089, plain, (![D_187, B_188]: (~m1_subset_1(D_187, k1_zfmisc_1(u1_struct_0(B_188))) | ~l1_pre_topc(B_188))), inference(splitLeft, [status(thm)], [c_36])).
% 27.91/18.73  tff(c_2092, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1985, c_2089])).
% 27.91/18.73  tff(c_2150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2092])).
% 27.91/18.73  tff(c_2186, plain, (![C_195, A_196]: (v3_pre_topc(C_195, A_196) | k1_tops_1(A_196, C_195)!=C_195 | ~m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196))), inference(splitRight, [status(thm)], [c_36])).
% 27.91/18.73  tff(c_2245, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2186])).
% 27.91/18.73  tff(c_2286, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2245])).
% 27.91/18.73  tff(c_2287, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_2286])).
% 27.91/18.73  tff(c_387, plain, (![A_104, B_105, C_106]: (k7_subset_1(A_104, B_105, C_106)=k4_xboole_0(B_105, C_106) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.91/18.73  tff(c_403, plain, (![C_106]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_106)=k4_xboole_0('#skF_2', C_106))), inference(resolution, [status(thm)], [c_42, c_387])).
% 27.91/18.73  tff(c_1395, plain, (![A_156, B_157]: (k7_subset_1(u1_struct_0(A_156), B_157, k2_tops_1(A_156, B_157))=k1_tops_1(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_128])).
% 27.91/18.73  tff(c_1429, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1395])).
% 27.91/18.73  tff(c_1456, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_403, c_1429])).
% 27.91/18.73  tff(c_478, plain, (![B_113, A_114]: (r1_tarski(B_113, k2_pre_topc(A_114, B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_85])).
% 27.91/18.73  tff(c_489, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_478])).
% 27.91/18.73  tff(c_501, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_489])).
% 27.91/18.73  tff(c_1193, plain, (![A_151, B_152]: (m1_subset_1(k2_pre_topc(A_151, B_152), k1_zfmisc_1(u1_struct_0(A_151))) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_78])).
% 27.91/18.73  tff(c_16, plain, (![A_15, B_16, C_17]: (k7_subset_1(A_15, B_16, C_17)=k4_xboole_0(B_16, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.91/18.73  tff(c_12542, plain, (![A_434, B_435, C_436]: (k7_subset_1(u1_struct_0(A_434), k2_pre_topc(A_434, B_435), C_436)=k4_xboole_0(k2_pre_topc(A_434, B_435), C_436) | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0(A_434))) | ~l1_pre_topc(A_434))), inference(resolution, [status(thm)], [c_1193, c_16])).
% 27.91/18.73  tff(c_12650, plain, (![C_436]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_436)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_436) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_12542])).
% 27.91/18.73  tff(c_13004, plain, (![C_441]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_441)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_441))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12650])).
% 27.91/18.73  tff(c_13033, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13004, c_127])).
% 27.91/18.73  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.91/18.73  tff(c_136, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.91/18.73  tff(c_149, plain, (![B_24, A_23]: (k4_xboole_0(B_24, A_23)=k3_subset_1(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_136])).
% 27.91/18.73  tff(c_508, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_501, c_149])).
% 27.91/18.73  tff(c_13132, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13033, c_508])).
% 27.91/18.73  tff(c_153, plain, (![A_84, B_85]: (k3_subset_1(A_84, k3_subset_1(A_84, B_85))=B_85 | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.91/18.73  tff(c_162, plain, (![B_24, A_23]: (k3_subset_1(B_24, k3_subset_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_153])).
% 27.91/18.73  tff(c_13196, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13132, c_162])).
% 27.91/18.73  tff(c_13202, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_501, c_13196])).
% 27.91/18.73  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.91/18.73  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.91/18.73  tff(c_55, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 27.91/18.73  tff(c_1039, plain, (![A_141, C_142]: (k7_subset_1(A_141, A_141, C_142)=k4_xboole_0(A_141, C_142))), inference(resolution, [status(thm)], [c_55, c_387])).
% 27.91/18.73  tff(c_10, plain, (![A_7, B_8, C_9]: (m1_subset_1(k7_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.91/18.73  tff(c_1052, plain, (![A_141, C_142]: (m1_subset_1(k4_xboole_0(A_141, C_142), k1_zfmisc_1(A_141)) | ~m1_subset_1(A_141, k1_zfmisc_1(A_141)))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_10])).
% 27.91/18.73  tff(c_1065, plain, (![A_141, C_142]: (m1_subset_1(k4_xboole_0(A_141, C_142), k1_zfmisc_1(A_141)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1052])).
% 27.91/18.73  tff(c_2298, plain, (m1_subset_1(k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_508, c_1065])).
% 27.91/18.73  tff(c_13178, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13132, c_2298])).
% 27.91/18.73  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.91/18.73  tff(c_13332, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13202, c_8])).
% 27.91/18.73  tff(c_13345, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13178, c_13332])).
% 27.91/18.73  tff(c_311, plain, (![A_94, B_95]: (m1_subset_1(k3_subset_1(A_94, B_95), k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.91/18.73  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k3_subset_1(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.91/18.73  tff(c_335, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k3_subset_1(A_94, B_95))=k3_subset_1(A_94, k3_subset_1(A_94, B_95)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_311, c_4])).
% 27.91/18.73  tff(c_13358, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'))), inference(resolution, [status(thm)], [c_13345, c_335])).
% 27.91/18.73  tff(c_13386, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13202, c_13132, c_13132, c_13358])).
% 27.91/18.73  tff(c_404, plain, (![A_4, C_106]: (k7_subset_1(A_4, A_4, C_106)=k4_xboole_0(A_4, C_106))), inference(resolution, [status(thm)], [c_55, c_387])).
% 27.91/18.73  tff(c_10964, plain, (![A_402, B_403, C_404, C_405]: (k7_subset_1(A_402, k7_subset_1(A_402, B_403, C_404), C_405)=k4_xboole_0(k7_subset_1(A_402, B_403, C_404), C_405) | ~m1_subset_1(B_403, k1_zfmisc_1(A_402)))), inference(resolution, [status(thm)], [c_10, c_387])).
% 27.91/18.73  tff(c_11064, plain, (![A_4, C_404, C_405]: (k7_subset_1(A_4, k7_subset_1(A_4, A_4, C_404), C_405)=k4_xboole_0(k7_subset_1(A_4, A_4, C_404), C_405))), inference(resolution, [status(thm)], [c_55, c_10964])).
% 27.91/18.73  tff(c_20302, plain, (![A_558, C_559, C_560]: (k7_subset_1(A_558, k4_xboole_0(A_558, C_559), C_560)=k4_xboole_0(k4_xboole_0(A_558, C_559), C_560))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_404, c_11064])).
% 27.91/18.73  tff(c_358, plain, (![A_96, B_97, C_98]: (r1_tarski(k7_subset_1(A_96, B_97, C_98), A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(resolution, [status(thm)], [c_341, c_22])).
% 27.91/18.73  tff(c_20353, plain, (![A_558, C_559, C_560]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_558, C_559), C_560), A_558) | ~m1_subset_1(k4_xboole_0(A_558, C_559), k1_zfmisc_1(A_558)))), inference(superposition, [status(thm), theory('equality')], [c_20302, c_358])).
% 27.91/18.73  tff(c_20510, plain, (![A_561, C_562, C_563]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_561, C_562), C_563), A_561))), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_20353])).
% 27.91/18.73  tff(c_20790, plain, (![C_566]: (r1_tarski(k4_xboole_0('#skF_2', C_566), k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_13386, c_20510])).
% 27.91/18.73  tff(c_20825, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_20790])).
% 27.91/18.73  tff(c_34, plain, (![A_35, B_37]: (k7_subset_1(u1_struct_0(A_35), k2_pre_topc(A_35, B_37), k1_tops_1(A_35, B_37))=k2_tops_1(A_35, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 27.91/18.73  tff(c_13024, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13004, c_34])).
% 27.91/18.73  tff(c_13058, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_13024])).
% 27.91/18.73  tff(c_20356, plain, (![A_558, C_559, C_560]: (m1_subset_1(k4_xboole_0(k4_xboole_0(A_558, C_559), C_560), k1_zfmisc_1(A_558)) | ~m1_subset_1(k4_xboole_0(A_558, C_559), k1_zfmisc_1(A_558)))), inference(superposition, [status(thm), theory('equality')], [c_20302, c_10])).
% 27.91/18.73  tff(c_20873, plain, (![A_567, C_568, C_569]: (m1_subset_1(k4_xboole_0(k4_xboole_0(A_567, C_568), C_569), k1_zfmisc_1(A_567)))), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_20356])).
% 27.91/18.73  tff(c_21451, plain, (![C_574]: (m1_subset_1(k4_xboole_0('#skF_2', C_574), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_13386, c_20873])).
% 27.91/18.73  tff(c_21509, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_21451])).
% 27.91/18.73  tff(c_21609, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_21509, c_4])).
% 27.91/18.73  tff(c_21626, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13058, c_21609])).
% 27.91/18.73  tff(c_66626, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_21626, c_162])).
% 27.91/18.73  tff(c_66670, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20825, c_13202, c_66626])).
% 27.91/18.73  tff(c_66672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2287, c_66670])).
% 27.91/18.73  tff(c_66673, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 27.91/18.73  tff(c_66674, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 27.91/18.73  tff(c_66949, plain, (![A_1139, B_1140, C_1141]: (k7_subset_1(A_1139, B_1140, C_1141)=k4_xboole_0(B_1140, C_1141) | ~m1_subset_1(B_1140, k1_zfmisc_1(A_1139)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.91/18.73  tff(c_66962, plain, (![C_1141]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1141)=k4_xboole_0('#skF_2', C_1141))), inference(resolution, [status(thm)], [c_42, c_66949])).
% 27.91/18.73  tff(c_67574, plain, (![A_1175, B_1176]: (k7_subset_1(u1_struct_0(A_1175), B_1176, k2_tops_1(A_1175, B_1176))=k1_tops_1(A_1175, B_1176) | ~m1_subset_1(B_1176, k1_zfmisc_1(u1_struct_0(A_1175))) | ~l1_pre_topc(A_1175))), inference(cnfTransformation, [status(thm)], [f_128])).
% 27.91/18.73  tff(c_67610, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_67574])).
% 27.91/18.73  tff(c_67640, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_66962, c_67610])).
% 27.91/18.73  tff(c_67038, plain, (![C_1151]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1151)=k4_xboole_0('#skF_2', C_1151))), inference(resolution, [status(thm)], [c_42, c_66949])).
% 27.91/18.73  tff(c_67044, plain, (![C_1151]: (m1_subset_1(k4_xboole_0('#skF_2', C_1151), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_67038, c_10])).
% 27.91/18.73  tff(c_67050, plain, (![C_1151]: (m1_subset_1(k4_xboole_0('#skF_2', C_1151), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67044])).
% 27.91/18.73  tff(c_67651, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_67640, c_67050])).
% 27.91/18.73  tff(c_38, plain, (![B_46, D_52, C_50, A_38]: (k1_tops_1(B_46, D_52)=D_52 | ~v3_pre_topc(D_52, B_46) | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(B_46))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(B_46) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 27.91/18.73  tff(c_68119, plain, (![C_1209, A_1210]: (~m1_subset_1(C_1209, k1_zfmisc_1(u1_struct_0(A_1210))) | ~l1_pre_topc(A_1210) | ~v2_pre_topc(A_1210))), inference(splitLeft, [status(thm)], [c_38])).
% 27.91/18.73  tff(c_68122, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_67651, c_68119])).
% 27.91/18.73  tff(c_68177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_68122])).
% 27.91/18.73  tff(c_68379, plain, (![B_1223, D_1224]: (k1_tops_1(B_1223, D_1224)=D_1224 | ~v3_pre_topc(D_1224, B_1223) | ~m1_subset_1(D_1224, k1_zfmisc_1(u1_struct_0(B_1223))) | ~l1_pre_topc(B_1223))), inference(splitRight, [status(thm)], [c_38])).
% 27.91/18.73  tff(c_68436, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_68379])).
% 27.91/18.73  tff(c_68472, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_66674, c_68436])).
% 27.91/18.73  tff(c_68495, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68472, c_34])).
% 27.91/18.73  tff(c_68499, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_68495])).
% 27.91/18.73  tff(c_68501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66673, c_68499])).
% 27.91/18.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.91/18.73  
% 27.91/18.73  Inference rules
% 27.91/18.73  ----------------------
% 27.91/18.73  #Ref     : 0
% 27.91/18.73  #Sup     : 16947
% 27.91/18.73  #Fact    : 0
% 27.91/18.73  #Define  : 0
% 27.91/18.73  #Split   : 9
% 27.91/18.73  #Chain   : 0
% 27.91/18.73  #Close   : 0
% 27.91/18.73  
% 27.91/18.73  Ordering : KBO
% 27.91/18.73  
% 27.91/18.73  Simplification rules
% 27.91/18.73  ----------------------
% 27.91/18.73  #Subsume      : 701
% 27.91/18.73  #Demod        : 11210
% 27.91/18.73  #Tautology    : 5095
% 27.91/18.73  #SimpNegUnit  : 16
% 27.91/18.73  #BackRed      : 29
% 27.91/18.73  
% 27.91/18.73  #Partial instantiations: 0
% 27.91/18.73  #Strategies tried      : 1
% 27.91/18.73  
% 27.91/18.73  Timing (in seconds)
% 27.91/18.73  ----------------------
% 27.91/18.74  Preprocessing        : 0.33
% 27.91/18.74  Parsing              : 0.18
% 27.91/18.74  CNF conversion       : 0.02
% 27.91/18.74  Main loop            : 17.62
% 27.91/18.74  Inferencing          : 2.32
% 27.91/18.74  Reduction            : 9.73
% 27.91/18.74  Demodulation         : 8.54
% 27.91/18.74  BG Simplification    : 0.27
% 27.91/18.74  Subsumption          : 4.19
% 27.91/18.74  Abstraction          : 0.44
% 27.91/18.74  MUC search           : 0.00
% 27.91/18.74  Cooper               : 0.00
% 27.91/18.74  Total                : 18.00
% 27.91/18.74  Index Insertion      : 0.00
% 27.91/18.74  Index Deletion       : 0.00
% 27.91/18.74  Index Matching       : 0.00
% 27.91/18.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
