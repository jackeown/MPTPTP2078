%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:43 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  194 (1267 expanded)
%              Number of leaves         :   42 ( 454 expanded)
%              Depth                    :   16
%              Number of atoms          :  338 (2448 expanded)
%              Number of equality atoms :  123 ( 778 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_54,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_138,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_195,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_48])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_179,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_188,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_184])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_189,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_44])).

tff(c_379,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_387,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_189,c_379])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_425,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_10])).

tff(c_465,plain,(
    ! [A_64,B_65] :
      ( k3_subset_1(A_64,k3_subset_1(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_471,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_189,c_465])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2289,plain,(
    ! [B_117,A_118] :
      ( k3_subset_1(B_117,k3_subset_1(B_117,A_118)) = A_118
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(resolution,[status(thm)],[c_26,c_465])).

tff(c_40,plain,(
    ! [B_33,A_31] :
      ( v2_tops_1(B_33,A_31)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_31),B_33),A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8454,plain,(
    ! [A_226,A_227] :
      ( v2_tops_1(k3_subset_1(u1_struct_0(A_226),A_227),A_226)
      | ~ v1_tops_1(A_227,A_226)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_226),A_227),k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226)
      | ~ r1_tarski(A_227,u1_struct_0(A_226)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_40])).

tff(c_8492,plain,(
    ! [A_227] :
      ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),A_227),'#skF_1')
      | ~ v1_tops_1(A_227,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),A_227),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_227,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_8454])).

tff(c_8515,plain,(
    ! [A_228] :
      ( v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),A_228),'#skF_1')
      | ~ v1_tops_1(A_228,'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_228),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_228,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_46,c_188,c_188,c_8492])).

tff(c_8559,plain,
    ( v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_8515])).

tff(c_8587,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_189,c_471,c_8559])).

tff(c_8588,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_8587])).

tff(c_1803,plain,(
    ! [A_110,B_111] :
      ( k3_subset_1(u1_struct_0(A_110),k2_pre_topc(A_110,k3_subset_1(u1_struct_0(A_110),B_111))) = k1_tops_1(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1824,plain,(
    ! [B_111] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_111))) = k1_tops_1('#skF_1',B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_1803])).

tff(c_2642,plain,(
    ! [B_127] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_127))) = k1_tops_1('#skF_1',B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_188,c_188,c_1824])).

tff(c_2674,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_2642])).

tff(c_3149,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2674])).

tff(c_3542,plain,(
    ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_3149])).

tff(c_3546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_3542])).

tff(c_3548,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2674])).

tff(c_14,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_56,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_55])).

tff(c_34,plain,(
    ! [A_25,B_27] :
      ( k3_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,k3_subset_1(u1_struct_0(A_25),B_27))) = k1_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9842,plain,(
    ! [A_240,A_241] :
      ( k3_subset_1(u1_struct_0(A_240),k2_pre_topc(A_240,A_241)) = k1_tops_1(A_240,k3_subset_1(u1_struct_0(A_240),A_241))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_240),A_241),k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ r1_tarski(A_241,u1_struct_0(A_240)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_34])).

tff(c_9877,plain,(
    ! [A_241] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_241)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_241))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_241),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_241,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_9842])).

tff(c_9941,plain,(
    ! [A_243] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_243)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_243))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_243),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_243,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_46,c_188,c_188,c_188,c_9877])).

tff(c_9988,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_9941])).

tff(c_10018,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_189,c_138,c_471,c_9988])).

tff(c_504,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k2_pre_topc(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k3_subset_1(A_16,k3_subset_1(A_16,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5919,plain,(
    ! [A_190,B_191] :
      ( k3_subset_1(u1_struct_0(A_190),k3_subset_1(u1_struct_0(A_190),k2_pre_topc(A_190,B_191))) = k2_pre_topc(A_190,B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(resolution,[status(thm)],[c_504,c_20])).

tff(c_5952,plain,(
    ! [B_191] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_191))) = k2_pre_topc('#skF_1',B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_5919])).

tff(c_5962,plain,(
    ! [B_191] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_191))) = k2_pre_topc('#skF_1',B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_188,c_188,c_5952])).

tff(c_10226,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10018,c_5962])).

tff(c_10259,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_56,c_10226])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_656,plain,(
    ! [A_76,B_77] : k3_xboole_0(k4_xboole_0(A_76,B_77),A_76) = k4_xboole_0(A_76,B_77) ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_962,plain,(
    ! [B_89,B_90] : k3_xboole_0(B_89,k4_xboole_0(B_89,B_90)) = k4_xboole_0(B_89,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_656])).

tff(c_1008,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_962])).

tff(c_1029,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_1008])).

tff(c_693,plain,(
    k3_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_656])).

tff(c_716,plain,(
    k3_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_693])).

tff(c_315,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_336,plain,(
    ! [A_59,B_60] : r1_tarski(k3_xboole_0(A_59,B_60),A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_10])).

tff(c_882,plain,(
    ! [B_84,A_85] :
      ( v1_tops_1(B_84,A_85)
      | k2_pre_topc(A_85,B_84) != k2_struct_0(A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4383,plain,(
    ! [A_163,A_164] :
      ( v1_tops_1(A_163,A_164)
      | k2_pre_topc(A_164,A_163) != k2_struct_0(A_164)
      | ~ l1_pre_topc(A_164)
      | ~ r1_tarski(A_163,u1_struct_0(A_164)) ) ),
    inference(resolution,[status(thm)],[c_26,c_882])).

tff(c_6610,plain,(
    ! [A_199,B_200] :
      ( v1_tops_1(k3_xboole_0(u1_struct_0(A_199),B_200),A_199)
      | k2_pre_topc(A_199,k3_xboole_0(u1_struct_0(A_199),B_200)) != k2_struct_0(A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_336,c_4383])).

tff(c_6637,plain,(
    ! [B_200] :
      ( v1_tops_1(k3_xboole_0(k2_struct_0('#skF_1'),B_200),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(u1_struct_0('#skF_1'),B_200)) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6610])).

tff(c_6662,plain,(
    ! [B_201] :
      ( v1_tops_1(k3_xboole_0(k2_struct_0('#skF_1'),B_201),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(k2_struct_0('#skF_1'),B_201)) != k2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_188,c_6637])).

tff(c_11426,plain,(
    ! [A_256] :
      ( v1_tops_1(k3_xboole_0(A_256,k2_struct_0('#skF_1')),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(k2_struct_0('#skF_1'),A_256)) != k2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6662])).

tff(c_11455,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) != k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_11426])).

tff(c_11512,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10259,c_1029,c_11455])).

tff(c_11514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8588,c_11512])).

tff(c_11516,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11678,plain,(
    ! [A_272,B_273] : k4_xboole_0(A_272,k4_xboole_0(A_272,B_273)) = k3_xboole_0(A_272,B_273) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11842,plain,(
    ! [A_277,B_278] : r1_tarski(k3_xboole_0(A_277,B_278),A_277) ),
    inference(superposition,[status(thm),theory(equality)],[c_11678,c_10])).

tff(c_11860,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_11842])).

tff(c_11815,plain,(
    ! [A_275,B_276] :
      ( k4_xboole_0(A_275,B_276) = k3_subset_1(A_275,B_276)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(A_275)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13906,plain,(
    ! [B_336,A_337] :
      ( k4_xboole_0(B_336,A_337) = k3_subset_1(B_336,A_337)
      | ~ r1_tarski(A_337,B_336) ) ),
    inference(resolution,[status(thm)],[c_26,c_11815])).

tff(c_13927,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = k3_subset_1(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11860,c_13906])).

tff(c_13957,plain,(
    ! [A_338] : k4_xboole_0(A_338,k1_xboole_0) = A_338 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13927])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11580,plain,(
    ! [A_264,B_265] :
      ( k3_xboole_0(A_264,B_265) = A_264
      | ~ r1_tarski(A_264,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12048,plain,(
    ! [A_288,B_289] : k3_xboole_0(k4_xboole_0(A_288,B_289),A_288) = k4_xboole_0(A_288,B_289) ),
    inference(resolution,[status(thm)],[c_10,c_11580])).

tff(c_11593,plain,(
    ! [A_266,B_267] : k5_xboole_0(A_266,k3_xboole_0(A_266,B_267)) = k4_xboole_0(A_266,B_267) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_11611,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11593])).

tff(c_12054,plain,(
    ! [A_288,B_289] : k5_xboole_0(A_288,k4_xboole_0(A_288,B_289)) = k4_xboole_0(A_288,k4_xboole_0(A_288,B_289)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12048,c_11611])).

tff(c_12105,plain,(
    ! [A_288,B_289] : k5_xboole_0(A_288,k4_xboole_0(A_288,B_289)) = k3_xboole_0(A_288,B_289) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12054])).

tff(c_13963,plain,(
    ! [A_338] : k5_xboole_0(A_338,A_338) = k3_xboole_0(A_338,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13957,c_12105])).

tff(c_13994,plain,(
    ! [A_338] : k5_xboole_0(A_338,A_338) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13963])).

tff(c_11555,plain,(
    ! [A_258] :
      ( u1_struct_0(A_258) = k2_struct_0(A_258)
      | ~ l1_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11560,plain,(
    ! [A_259] :
      ( u1_struct_0(A_259) = k2_struct_0(A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_32,c_11555])).

tff(c_11564,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_11560])).

tff(c_11565,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11564,c_44])).

tff(c_11823,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_11565,c_11815])).

tff(c_11833,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11823,c_10])).

tff(c_11515,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11863,plain,(
    ! [A_279,B_280] :
      ( k3_subset_1(A_279,k3_subset_1(A_279,B_280)) = B_280
      | ~ m1_subset_1(B_280,k1_zfmisc_1(A_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11869,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11565,c_11863])).

tff(c_13666,plain,(
    ! [B_330,A_331] :
      ( k3_subset_1(B_330,k3_subset_1(B_330,A_331)) = A_331
      | ~ r1_tarski(A_331,B_330) ) ),
    inference(resolution,[status(thm)],[c_26,c_11863])).

tff(c_42,plain,(
    ! [A_31,B_33] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_31),B_33),A_31)
      | ~ v2_tops_1(B_33,A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20147,plain,(
    ! [A_446,A_447] :
      ( v1_tops_1(A_446,A_447)
      | ~ v2_tops_1(k3_subset_1(u1_struct_0(A_447),A_446),A_447)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_447),A_446),k1_zfmisc_1(u1_struct_0(A_447)))
      | ~ l1_pre_topc(A_447)
      | ~ r1_tarski(A_446,u1_struct_0(A_447)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13666,c_42])).

tff(c_20185,plain,(
    ! [A_446] :
      ( v1_tops_1(A_446,'#skF_1')
      | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),A_446),'#skF_1')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),A_446),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_446,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_20147])).

tff(c_20270,plain,(
    ! [A_450] :
      ( v1_tops_1(A_450,'#skF_1')
      | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),A_450),'#skF_1')
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_450),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_450,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11564,c_46,c_11564,c_11564,c_20185])).

tff(c_20314,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11869,c_20270])).

tff(c_20344,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11833,c_11565,c_11515,c_11869,c_20314])).

tff(c_12309,plain,(
    ! [A_299,B_300] :
      ( k2_pre_topc(A_299,B_300) = k2_struct_0(A_299)
      | ~ v1_tops_1(B_300,A_299)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16122,plain,(
    ! [A_384,A_385] :
      ( k2_pre_topc(A_384,A_385) = k2_struct_0(A_384)
      | ~ v1_tops_1(A_385,A_384)
      | ~ l1_pre_topc(A_384)
      | ~ r1_tarski(A_385,u1_struct_0(A_384)) ) ),
    inference(resolution,[status(thm)],[c_26,c_12309])).

tff(c_18650,plain,(
    ! [A_423,B_424] :
      ( k2_pre_topc(A_423,k4_xboole_0(u1_struct_0(A_423),B_424)) = k2_struct_0(A_423)
      | ~ v1_tops_1(k4_xboole_0(u1_struct_0(A_423),B_424),A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(resolution,[status(thm)],[c_10,c_16122])).

tff(c_18676,plain,(
    ! [B_424] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(u1_struct_0('#skF_1'),B_424)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'),B_424),'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_18650])).

tff(c_19105,plain,(
    ! [B_428] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),B_428)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'),B_428),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11564,c_18676])).

tff(c_19133,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11823,c_19105])).

tff(c_19148,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11823,c_19133])).

tff(c_24327,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20344,c_19148])).

tff(c_21053,plain,(
    ! [A_453,A_454] :
      ( k3_subset_1(u1_struct_0(A_453),k2_pre_topc(A_453,A_454)) = k1_tops_1(A_453,k3_subset_1(u1_struct_0(A_453),A_454))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_453),A_454),k1_zfmisc_1(u1_struct_0(A_453)))
      | ~ l1_pre_topc(A_453)
      | ~ r1_tarski(A_454,u1_struct_0(A_453)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13666,c_34])).

tff(c_21091,plain,(
    ! [A_454] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_454)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_454))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),A_454),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_454,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_21053])).

tff(c_21844,plain,(
    ! [A_466] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_466)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_466))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_466),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_466,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11564,c_46,c_11564,c_11564,c_11564,c_21091])).

tff(c_21891,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11869,c_21844])).

tff(c_21921,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11833,c_11565,c_11869,c_21891])).

tff(c_11932,plain,(
    ! [A_284,B_285] :
      ( m1_subset_1(k2_pre_topc(A_284,B_285),k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k3_subset_1(A_14,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17118,plain,(
    ! [A_404,B_405] :
      ( k4_xboole_0(u1_struct_0(A_404),k2_pre_topc(A_404,B_405)) = k3_subset_1(u1_struct_0(A_404),k2_pre_topc(A_404,B_405))
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_11932,c_18])).

tff(c_19240,plain,(
    ! [A_432,A_433] :
      ( k4_xboole_0(u1_struct_0(A_432),k2_pre_topc(A_432,A_433)) = k3_subset_1(u1_struct_0(A_432),k2_pre_topc(A_432,A_433))
      | ~ l1_pre_topc(A_432)
      | ~ r1_tarski(A_433,u1_struct_0(A_432)) ) ),
    inference(resolution,[status(thm)],[c_26,c_17118])).

tff(c_19276,plain,(
    ! [A_433] :
      ( k4_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_433)) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_433))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_433,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_19240])).

tff(c_19283,plain,(
    ! [A_434] :
      ( k4_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_434)) = k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_434))
      | ~ r1_tarski(A_434,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11564,c_46,c_11564,c_19276])).

tff(c_19316,plain,(
    ! [A_434] :
      ( r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_434)),k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_434,k2_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19283,c_10])).

tff(c_22788,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_struct_0('#skF_1'))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21921,c_19316])).

tff(c_22828,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11833,c_22788])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22857,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22828,c_6])).

tff(c_22960,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22857,c_2])).

tff(c_13208,plain,(
    ! [A_323,B_324] :
      ( k3_subset_1(u1_struct_0(A_323),k2_pre_topc(A_323,k3_subset_1(u1_struct_0(A_323),B_324))) = k1_tops_1(A_323,B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_13229,plain,(
    ! [B_324] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_324))) = k1_tops_1('#skF_1',B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_13208])).

tff(c_14017,plain,(
    ! [B_340] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_340))) = k1_tops_1('#skF_1',B_340)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11564,c_11564,c_13229])).

tff(c_14049,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11869,c_14017])).

tff(c_14428,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14049])).

tff(c_14952,plain,(
    ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_14428])).

tff(c_14956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11833,c_14952])).

tff(c_14958,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14049])).

tff(c_16413,plain,(
    ! [A_390,B_391] :
      ( k3_subset_1(u1_struct_0(A_390),k3_subset_1(u1_struct_0(A_390),k2_pre_topc(A_390,B_391))) = k2_pre_topc(A_390,B_391)
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(resolution,[status(thm)],[c_11932,c_20])).

tff(c_23025,plain,(
    ! [A_475,B_476] :
      ( k3_subset_1(u1_struct_0(A_475),k1_tops_1(A_475,B_476)) = k2_pre_topc(A_475,k3_subset_1(u1_struct_0(A_475),B_476))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_475),B_476),k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ l1_pre_topc(A_475)
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ l1_pre_topc(A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_16413])).

tff(c_23060,plain,(
    ! [B_476] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_476)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_476))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_476),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11564,c_23025])).

tff(c_23081,plain,(
    ! [B_477] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_477)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_477))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_477),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11564,c_46,c_11564,c_11564,c_11564,c_23060])).

tff(c_23112,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14958,c_23081])).

tff(c_23152,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11565,c_23112])).

tff(c_11822,plain,(
    ! [B_20,A_19] :
      ( k4_xboole_0(B_20,A_19) = k3_subset_1(B_20,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_11815])).

tff(c_22856,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22828,c_11822])).

tff(c_23555,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23152,c_22856])).

tff(c_23571,plain,(
    k5_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k3_xboole_0(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23555,c_12105])).

tff(c_23589,plain,(
    k5_xboole_0(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22960,c_23571])).

tff(c_24330,plain,(
    k5_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24327,c_23589])).

tff(c_24337,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13994,c_24330])).

tff(c_24339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11516,c_24337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:20:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.54/4.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.48  
% 11.54/4.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.48  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.54/4.48  
% 11.54/4.48  %Foreground sorts:
% 11.54/4.48  
% 11.54/4.48  
% 11.54/4.48  %Background operators:
% 11.54/4.48  
% 11.54/4.48  
% 11.54/4.48  %Foreground operators:
% 11.54/4.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.54/4.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.54/4.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.54/4.48  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 11.54/4.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.54/4.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.54/4.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.54/4.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.54/4.48  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 11.54/4.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.54/4.48  tff('#skF_2', type, '#skF_2': $i).
% 11.54/4.48  tff('#skF_1', type, '#skF_1': $i).
% 11.54/4.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.54/4.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.54/4.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.54/4.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.54/4.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 11.54/4.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.54/4.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.54/4.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.54/4.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.54/4.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.54/4.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.54/4.48  
% 11.67/4.51  tff(f_106, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 11.67/4.51  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.67/4.51  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 11.67/4.51  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.67/4.51  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.67/4.51  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.67/4.51  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.67/4.51  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 11.67/4.51  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 11.67/4.51  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 11.67/4.51  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.67/4.51  tff(f_53, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 11.67/4.51  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.67/4.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.67/4.51  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.67/4.51  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.67/4.51  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 11.67/4.51  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.67/4.51  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.67/4.51  tff(c_54, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.67/4.51  tff(c_138, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 11.67/4.51  tff(c_48, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.67/4.51  tff(c_195, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_48])).
% 11.67/4.51  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.67/4.51  tff(c_32, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.67/4.51  tff(c_179, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.67/4.51  tff(c_184, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_32, c_179])).
% 11.67/4.51  tff(c_188, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_184])).
% 11.67/4.51  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.67/4.51  tff(c_189, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_44])).
% 11.67/4.51  tff(c_379, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.67/4.51  tff(c_387, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_189, c_379])).
% 11.67/4.51  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.67/4.51  tff(c_425, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_387, c_10])).
% 11.67/4.51  tff(c_465, plain, (![A_64, B_65]: (k3_subset_1(A_64, k3_subset_1(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.67/4.51  tff(c_471, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_189, c_465])).
% 11.67/4.51  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.67/4.51  tff(c_2289, plain, (![B_117, A_118]: (k3_subset_1(B_117, k3_subset_1(B_117, A_118))=A_118 | ~r1_tarski(A_118, B_117))), inference(resolution, [status(thm)], [c_26, c_465])).
% 11.67/4.51  tff(c_40, plain, (![B_33, A_31]: (v2_tops_1(B_33, A_31) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_31), B_33), A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.67/4.51  tff(c_8454, plain, (![A_226, A_227]: (v2_tops_1(k3_subset_1(u1_struct_0(A_226), A_227), A_226) | ~v1_tops_1(A_227, A_226) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_226), A_227), k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226) | ~r1_tarski(A_227, u1_struct_0(A_226)))), inference(superposition, [status(thm), theory('equality')], [c_2289, c_40])).
% 11.67/4.51  tff(c_8492, plain, (![A_227]: (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), A_227), '#skF_1') | ~v1_tops_1(A_227, '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), A_227), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_227, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_8454])).
% 11.67/4.51  tff(c_8515, plain, (![A_228]: (v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), A_228), '#skF_1') | ~v1_tops_1(A_228, '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_228), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_228, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_46, c_188, c_188, c_8492])).
% 11.67/4.51  tff(c_8559, plain, (v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_8515])).
% 11.67/4.51  tff(c_8587, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_189, c_471, c_8559])).
% 11.67/4.51  tff(c_8588, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_195, c_8587])).
% 11.67/4.51  tff(c_1803, plain, (![A_110, B_111]: (k3_subset_1(u1_struct_0(A_110), k2_pre_topc(A_110, k3_subset_1(u1_struct_0(A_110), B_111)))=k1_tops_1(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.67/4.51  tff(c_1824, plain, (![B_111]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_111)))=k1_tops_1('#skF_1', B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_1803])).
% 11.67/4.51  tff(c_2642, plain, (![B_127]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_127)))=k1_tops_1('#skF_1', B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_188, c_188, c_1824])).
% 11.67/4.51  tff(c_2674, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_471, c_2642])).
% 11.67/4.51  tff(c_3149, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2674])).
% 11.67/4.51  tff(c_3542, plain, (~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_3149])).
% 11.67/4.51  tff(c_3546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_425, c_3542])).
% 11.67/4.51  tff(c_3548, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2674])).
% 11.67/4.51  tff(c_14, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.67/4.51  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.67/4.51  tff(c_22, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.67/4.51  tff(c_55, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 11.67/4.51  tff(c_56, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_55])).
% 11.67/4.51  tff(c_34, plain, (![A_25, B_27]: (k3_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, k3_subset_1(u1_struct_0(A_25), B_27)))=k1_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.67/4.51  tff(c_9842, plain, (![A_240, A_241]: (k3_subset_1(u1_struct_0(A_240), k2_pre_topc(A_240, A_241))=k1_tops_1(A_240, k3_subset_1(u1_struct_0(A_240), A_241)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_240), A_241), k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240) | ~r1_tarski(A_241, u1_struct_0(A_240)))), inference(superposition, [status(thm), theory('equality')], [c_2289, c_34])).
% 11.67/4.51  tff(c_9877, plain, (![A_241]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_241))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), A_241)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_241), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_241, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_9842])).
% 11.67/4.51  tff(c_9941, plain, (![A_243]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_243))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), A_243)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_243), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_243, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_46, c_188, c_188, c_188, c_9877])).
% 11.67/4.51  tff(c_9988, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_9941])).
% 11.67/4.51  tff(c_10018, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_425, c_189, c_138, c_471, c_9988])).
% 11.67/4.51  tff(c_504, plain, (![A_68, B_69]: (m1_subset_1(k2_pre_topc(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.67/4.51  tff(c_20, plain, (![A_16, B_17]: (k3_subset_1(A_16, k3_subset_1(A_16, B_17))=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.67/4.51  tff(c_5919, plain, (![A_190, B_191]: (k3_subset_1(u1_struct_0(A_190), k3_subset_1(u1_struct_0(A_190), k2_pre_topc(A_190, B_191)))=k2_pre_topc(A_190, B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(resolution, [status(thm)], [c_504, c_20])).
% 11.67/4.51  tff(c_5952, plain, (![B_191]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_191)))=k2_pre_topc('#skF_1', B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_5919])).
% 11.67/4.51  tff(c_5962, plain, (![B_191]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_191)))=k2_pre_topc('#skF_1', B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_188, c_188, c_5952])).
% 11.67/4.51  tff(c_10226, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10018, c_5962])).
% 11.67/4.51  tff(c_10259, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_56, c_10226])).
% 11.67/4.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.67/4.51  tff(c_201, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.67/4.51  tff(c_656, plain, (![A_76, B_77]: (k3_xboole_0(k4_xboole_0(A_76, B_77), A_76)=k4_xboole_0(A_76, B_77))), inference(resolution, [status(thm)], [c_10, c_201])).
% 11.67/4.51  tff(c_962, plain, (![B_89, B_90]: (k3_xboole_0(B_89, k4_xboole_0(B_89, B_90))=k4_xboole_0(B_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_2, c_656])).
% 11.67/4.51  tff(c_1008, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_387, c_962])).
% 11.67/4.51  tff(c_1029, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_1008])).
% 11.67/4.51  tff(c_693, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_387, c_656])).
% 11.67/4.51  tff(c_716, plain, (k3_xboole_0(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_693])).
% 11.67/4.51  tff(c_315, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.67/4.51  tff(c_336, plain, (![A_59, B_60]: (r1_tarski(k3_xboole_0(A_59, B_60), A_59))), inference(superposition, [status(thm), theory('equality')], [c_315, c_10])).
% 11.67/4.51  tff(c_882, plain, (![B_84, A_85]: (v1_tops_1(B_84, A_85) | k2_pre_topc(A_85, B_84)!=k2_struct_0(A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.67/4.51  tff(c_4383, plain, (![A_163, A_164]: (v1_tops_1(A_163, A_164) | k2_pre_topc(A_164, A_163)!=k2_struct_0(A_164) | ~l1_pre_topc(A_164) | ~r1_tarski(A_163, u1_struct_0(A_164)))), inference(resolution, [status(thm)], [c_26, c_882])).
% 11.67/4.51  tff(c_6610, plain, (![A_199, B_200]: (v1_tops_1(k3_xboole_0(u1_struct_0(A_199), B_200), A_199) | k2_pre_topc(A_199, k3_xboole_0(u1_struct_0(A_199), B_200))!=k2_struct_0(A_199) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_336, c_4383])).
% 11.67/4.51  tff(c_6637, plain, (![B_200]: (v1_tops_1(k3_xboole_0(k2_struct_0('#skF_1'), B_200), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(u1_struct_0('#skF_1'), B_200))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_6610])).
% 11.67/4.51  tff(c_6662, plain, (![B_201]: (v1_tops_1(k3_xboole_0(k2_struct_0('#skF_1'), B_201), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(k2_struct_0('#skF_1'), B_201))!=k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_188, c_6637])).
% 11.67/4.51  tff(c_11426, plain, (![A_256]: (v1_tops_1(k3_xboole_0(A_256, k2_struct_0('#skF_1')), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(k2_struct_0('#skF_1'), A_256))!=k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6662])).
% 11.67/4.51  tff(c_11455, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))!=k2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_716, c_11426])).
% 11.67/4.51  tff(c_11512, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10259, c_1029, c_11455])).
% 11.67/4.51  tff(c_11514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8588, c_11512])).
% 11.67/4.51  tff(c_11516, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 11.67/4.51  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.67/4.51  tff(c_11678, plain, (![A_272, B_273]: (k4_xboole_0(A_272, k4_xboole_0(A_272, B_273))=k3_xboole_0(A_272, B_273))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.67/4.51  tff(c_11842, plain, (![A_277, B_278]: (r1_tarski(k3_xboole_0(A_277, B_278), A_277))), inference(superposition, [status(thm), theory('equality')], [c_11678, c_10])).
% 11.67/4.51  tff(c_11860, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_11842])).
% 11.67/4.51  tff(c_11815, plain, (![A_275, B_276]: (k4_xboole_0(A_275, B_276)=k3_subset_1(A_275, B_276) | ~m1_subset_1(B_276, k1_zfmisc_1(A_275)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.67/4.51  tff(c_13906, plain, (![B_336, A_337]: (k4_xboole_0(B_336, A_337)=k3_subset_1(B_336, A_337) | ~r1_tarski(A_337, B_336))), inference(resolution, [status(thm)], [c_26, c_11815])).
% 11.67/4.51  tff(c_13927, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=k3_subset_1(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_11860, c_13906])).
% 11.67/4.51  tff(c_13957, plain, (![A_338]: (k4_xboole_0(A_338, k1_xboole_0)=A_338)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_13927])).
% 11.67/4.51  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.67/4.51  tff(c_11580, plain, (![A_264, B_265]: (k3_xboole_0(A_264, B_265)=A_264 | ~r1_tarski(A_264, B_265))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.67/4.51  tff(c_12048, plain, (![A_288, B_289]: (k3_xboole_0(k4_xboole_0(A_288, B_289), A_288)=k4_xboole_0(A_288, B_289))), inference(resolution, [status(thm)], [c_10, c_11580])).
% 11.67/4.51  tff(c_11593, plain, (![A_266, B_267]: (k5_xboole_0(A_266, k3_xboole_0(A_266, B_267))=k4_xboole_0(A_266, B_267))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.67/4.51  tff(c_11611, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11593])).
% 11.67/4.51  tff(c_12054, plain, (![A_288, B_289]: (k5_xboole_0(A_288, k4_xboole_0(A_288, B_289))=k4_xboole_0(A_288, k4_xboole_0(A_288, B_289)))), inference(superposition, [status(thm), theory('equality')], [c_12048, c_11611])).
% 11.67/4.51  tff(c_12105, plain, (![A_288, B_289]: (k5_xboole_0(A_288, k4_xboole_0(A_288, B_289))=k3_xboole_0(A_288, B_289))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12054])).
% 11.67/4.51  tff(c_13963, plain, (![A_338]: (k5_xboole_0(A_338, A_338)=k3_xboole_0(A_338, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13957, c_12105])).
% 11.67/4.51  tff(c_13994, plain, (![A_338]: (k5_xboole_0(A_338, A_338)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13963])).
% 11.67/4.51  tff(c_11555, plain, (![A_258]: (u1_struct_0(A_258)=k2_struct_0(A_258) | ~l1_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.67/4.51  tff(c_11560, plain, (![A_259]: (u1_struct_0(A_259)=k2_struct_0(A_259) | ~l1_pre_topc(A_259))), inference(resolution, [status(thm)], [c_32, c_11555])).
% 11.67/4.51  tff(c_11564, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_11560])).
% 11.67/4.51  tff(c_11565, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11564, c_44])).
% 11.67/4.51  tff(c_11823, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_11565, c_11815])).
% 11.67/4.51  tff(c_11833, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11823, c_10])).
% 11.67/4.51  tff(c_11515, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 11.67/4.51  tff(c_11863, plain, (![A_279, B_280]: (k3_subset_1(A_279, k3_subset_1(A_279, B_280))=B_280 | ~m1_subset_1(B_280, k1_zfmisc_1(A_279)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.67/4.51  tff(c_11869, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_11565, c_11863])).
% 11.67/4.51  tff(c_13666, plain, (![B_330, A_331]: (k3_subset_1(B_330, k3_subset_1(B_330, A_331))=A_331 | ~r1_tarski(A_331, B_330))), inference(resolution, [status(thm)], [c_26, c_11863])).
% 11.67/4.51  tff(c_42, plain, (![A_31, B_33]: (v1_tops_1(k3_subset_1(u1_struct_0(A_31), B_33), A_31) | ~v2_tops_1(B_33, A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.67/4.51  tff(c_20147, plain, (![A_446, A_447]: (v1_tops_1(A_446, A_447) | ~v2_tops_1(k3_subset_1(u1_struct_0(A_447), A_446), A_447) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_447), A_446), k1_zfmisc_1(u1_struct_0(A_447))) | ~l1_pre_topc(A_447) | ~r1_tarski(A_446, u1_struct_0(A_447)))), inference(superposition, [status(thm), theory('equality')], [c_13666, c_42])).
% 11.67/4.51  tff(c_20185, plain, (![A_446]: (v1_tops_1(A_446, '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), A_446), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), A_446), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_446, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_20147])).
% 11.67/4.51  tff(c_20270, plain, (![A_450]: (v1_tops_1(A_450, '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), A_450), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_450), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_450, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11564, c_46, c_11564, c_11564, c_20185])).
% 11.67/4.51  tff(c_20314, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11869, c_20270])).
% 11.67/4.51  tff(c_20344, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11833, c_11565, c_11515, c_11869, c_20314])).
% 11.67/4.51  tff(c_12309, plain, (![A_299, B_300]: (k2_pre_topc(A_299, B_300)=k2_struct_0(A_299) | ~v1_tops_1(B_300, A_299) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.67/4.51  tff(c_16122, plain, (![A_384, A_385]: (k2_pre_topc(A_384, A_385)=k2_struct_0(A_384) | ~v1_tops_1(A_385, A_384) | ~l1_pre_topc(A_384) | ~r1_tarski(A_385, u1_struct_0(A_384)))), inference(resolution, [status(thm)], [c_26, c_12309])).
% 11.67/4.51  tff(c_18650, plain, (![A_423, B_424]: (k2_pre_topc(A_423, k4_xboole_0(u1_struct_0(A_423), B_424))=k2_struct_0(A_423) | ~v1_tops_1(k4_xboole_0(u1_struct_0(A_423), B_424), A_423) | ~l1_pre_topc(A_423))), inference(resolution, [status(thm)], [c_10, c_16122])).
% 11.67/4.51  tff(c_18676, plain, (![B_424]: (k2_pre_topc('#skF_1', k4_xboole_0(u1_struct_0('#skF_1'), B_424))=k2_struct_0('#skF_1') | ~v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'), B_424), '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_18650])).
% 11.67/4.51  tff(c_19105, plain, (![B_428]: (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), B_428))=k2_struct_0('#skF_1') | ~v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'), B_428), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_11564, c_18676])).
% 11.67/4.51  tff(c_19133, plain, (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11823, c_19105])).
% 11.67/4.51  tff(c_19148, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11823, c_19133])).
% 11.67/4.51  tff(c_24327, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20344, c_19148])).
% 11.67/4.51  tff(c_21053, plain, (![A_453, A_454]: (k3_subset_1(u1_struct_0(A_453), k2_pre_topc(A_453, A_454))=k1_tops_1(A_453, k3_subset_1(u1_struct_0(A_453), A_454)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_453), A_454), k1_zfmisc_1(u1_struct_0(A_453))) | ~l1_pre_topc(A_453) | ~r1_tarski(A_454, u1_struct_0(A_453)))), inference(superposition, [status(thm), theory('equality')], [c_13666, c_34])).
% 11.67/4.51  tff(c_21091, plain, (![A_454]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_454))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), A_454)) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), A_454), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_454, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_21053])).
% 11.67/4.51  tff(c_21844, plain, (![A_466]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_466))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), A_466)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_466), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_466, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11564, c_46, c_11564, c_11564, c_11564, c_21091])).
% 11.67/4.51  tff(c_21891, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11869, c_21844])).
% 11.67/4.51  tff(c_21921, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11833, c_11565, c_11869, c_21891])).
% 11.67/4.51  tff(c_11932, plain, (![A_284, B_285]: (m1_subset_1(k2_pre_topc(A_284, B_285), k1_zfmisc_1(u1_struct_0(A_284))) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.67/4.51  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k3_subset_1(A_14, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.67/4.51  tff(c_17118, plain, (![A_404, B_405]: (k4_xboole_0(u1_struct_0(A_404), k2_pre_topc(A_404, B_405))=k3_subset_1(u1_struct_0(A_404), k2_pre_topc(A_404, B_405)) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_11932, c_18])).
% 11.67/4.51  tff(c_19240, plain, (![A_432, A_433]: (k4_xboole_0(u1_struct_0(A_432), k2_pre_topc(A_432, A_433))=k3_subset_1(u1_struct_0(A_432), k2_pre_topc(A_432, A_433)) | ~l1_pre_topc(A_432) | ~r1_tarski(A_433, u1_struct_0(A_432)))), inference(resolution, [status(thm)], [c_26, c_17118])).
% 11.67/4.51  tff(c_19276, plain, (![A_433]: (k4_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_433))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_433)) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_433, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_19240])).
% 11.67/4.51  tff(c_19283, plain, (![A_434]: (k4_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_434))=k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_434)) | ~r1_tarski(A_434, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11564, c_46, c_11564, c_19276])).
% 11.67/4.51  tff(c_19316, plain, (![A_434]: (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_434)), k2_struct_0('#skF_1')) | ~r1_tarski(A_434, k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_19283, c_10])).
% 11.67/4.51  tff(c_22788, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_struct_0('#skF_1')) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_21921, c_19316])).
% 11.67/4.51  tff(c_22828, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11833, c_22788])).
% 11.67/4.51  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.67/4.51  tff(c_22857, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22828, c_6])).
% 11.67/4.51  tff(c_22960, plain, (k3_xboole_0(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22857, c_2])).
% 11.67/4.51  tff(c_13208, plain, (![A_323, B_324]: (k3_subset_1(u1_struct_0(A_323), k2_pre_topc(A_323, k3_subset_1(u1_struct_0(A_323), B_324)))=k1_tops_1(A_323, B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.67/4.51  tff(c_13229, plain, (![B_324]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_324)))=k1_tops_1('#skF_1', B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_13208])).
% 11.67/4.51  tff(c_14017, plain, (![B_340]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_340)))=k1_tops_1('#skF_1', B_340) | ~m1_subset_1(B_340, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_11564, c_11564, c_13229])).
% 11.67/4.51  tff(c_14049, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_11869, c_14017])).
% 11.67/4.51  tff(c_14428, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_14049])).
% 11.67/4.51  tff(c_14952, plain, (~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_14428])).
% 11.67/4.51  tff(c_14956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11833, c_14952])).
% 11.67/4.51  tff(c_14958, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_14049])).
% 11.67/4.51  tff(c_16413, plain, (![A_390, B_391]: (k3_subset_1(u1_struct_0(A_390), k3_subset_1(u1_struct_0(A_390), k2_pre_topc(A_390, B_391)))=k2_pre_topc(A_390, B_391) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(resolution, [status(thm)], [c_11932, c_20])).
% 11.67/4.51  tff(c_23025, plain, (![A_475, B_476]: (k3_subset_1(u1_struct_0(A_475), k1_tops_1(A_475, B_476))=k2_pre_topc(A_475, k3_subset_1(u1_struct_0(A_475), B_476)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_475), B_476), k1_zfmisc_1(u1_struct_0(A_475))) | ~l1_pre_topc(A_475) | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0(A_475))) | ~l1_pre_topc(A_475))), inference(superposition, [status(thm), theory('equality')], [c_34, c_16413])).
% 11.67/4.51  tff(c_23060, plain, (![B_476]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_476))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_476)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_476), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11564, c_23025])).
% 11.67/4.51  tff(c_23081, plain, (![B_477]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_477))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_477)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_477), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_477, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_11564, c_46, c_11564, c_11564, c_11564, c_23060])).
% 11.67/4.51  tff(c_23112, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14958, c_23081])).
% 11.67/4.51  tff(c_23152, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11565, c_23112])).
% 11.67/4.51  tff(c_11822, plain, (![B_20, A_19]: (k4_xboole_0(B_20, A_19)=k3_subset_1(B_20, A_19) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_26, c_11815])).
% 11.67/4.51  tff(c_22856, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22828, c_11822])).
% 11.67/4.51  tff(c_23555, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_23152, c_22856])).
% 11.67/4.51  tff(c_23571, plain, (k5_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k3_xboole_0(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_23555, c_12105])).
% 11.67/4.51  tff(c_23589, plain, (k5_xboole_0(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22960, c_23571])).
% 11.67/4.51  tff(c_24330, plain, (k5_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24327, c_23589])).
% 11.67/4.51  tff(c_24337, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13994, c_24330])).
% 11.67/4.51  tff(c_24339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11516, c_24337])).
% 11.67/4.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.51  
% 11.67/4.51  Inference rules
% 11.67/4.51  ----------------------
% 11.67/4.51  #Ref     : 0
% 11.67/4.51  #Sup     : 5836
% 11.67/4.51  #Fact    : 0
% 11.67/4.51  #Define  : 0
% 11.67/4.51  #Split   : 27
% 11.67/4.51  #Chain   : 0
% 11.67/4.51  #Close   : 0
% 11.67/4.51  
% 11.67/4.51  Ordering : KBO
% 11.67/4.51  
% 11.67/4.51  Simplification rules
% 11.67/4.51  ----------------------
% 11.67/4.51  #Subsume      : 508
% 11.67/4.51  #Demod        : 7412
% 11.67/4.51  #Tautology    : 3808
% 11.67/4.51  #SimpNegUnit  : 173
% 11.67/4.51  #BackRed      : 54
% 11.67/4.51  
% 11.67/4.51  #Partial instantiations: 0
% 11.67/4.51  #Strategies tried      : 1
% 11.67/4.51  
% 11.67/4.51  Timing (in seconds)
% 11.67/4.51  ----------------------
% 11.67/4.51  Preprocessing        : 0.31
% 11.67/4.51  Parsing              : 0.16
% 11.67/4.51  CNF conversion       : 0.02
% 11.67/4.51  Main loop            : 3.40
% 11.67/4.51  Inferencing          : 0.79
% 11.67/4.51  Reduction            : 1.74
% 11.67/4.51  Demodulation         : 1.44
% 11.67/4.51  BG Simplification    : 0.09
% 11.67/4.51  Subsumption          : 0.56
% 11.67/4.51  Abstraction          : 0.14
% 11.67/4.51  MUC search           : 0.00
% 11.67/4.51  Cooper               : 0.00
% 11.67/4.51  Total                : 3.78
% 11.67/4.51  Index Insertion      : 0.00
% 11.67/4.51  Index Deletion       : 0.00
% 11.67/4.51  Index Matching       : 0.00
% 11.67/4.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
