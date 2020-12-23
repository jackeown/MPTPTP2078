%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 157 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 258 expanded)
%              Number of equality atoms :   49 (  81 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_128,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_591,plain,(
    ! [B_62,A_63] :
      ( v2_tops_1(B_62,A_63)
      | k1_tops_1(A_63,B_62) != k1_xboole_0
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_594,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_591])).

tff(c_597,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_594])).

tff(c_598,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_597])).

tff(c_147,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_31,B_32] : r1_tarski(k4_xboole_0(A_31,B_32),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [B_32] : k4_xboole_0(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_10])).

tff(c_184,plain,(
    ! [B_45] : k3_xboole_0(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_57])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_196,plain,(
    ! [B_45] : k3_xboole_0(B_45,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_147])).

tff(c_374,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_176])).

tff(c_38,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_138,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_38])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_138,c_4])).

tff(c_180,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    ! [C_44] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_44) = k4_xboole_0('#skF_2',C_44) ),
    inference(resolution,[status(thm)],[c_28,c_180])).

tff(c_1171,plain,(
    ! [A_78,B_79] :
      ( k7_subset_1(u1_struct_0(A_78),B_79,k2_tops_1(A_78,B_79)) = k1_tops_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1175,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1171])).

tff(c_1179,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_183,c_1175])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1189,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_12])).

tff(c_1197,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1189])).

tff(c_1212,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_12])).

tff(c_1220,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_1212])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_5,B_6] : k3_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k4_xboole_0(A_5,B_6) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_1186,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_127])).

tff(c_1196,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_2,c_1186])).

tff(c_1263,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1196])).

tff(c_1264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_1263])).

tff(c_1265,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1266,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1793,plain,(
    ! [A_107,B_108] :
      ( k1_tops_1(A_107,B_108) = k1_xboole_0
      | ~ v2_tops_1(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1796,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1793])).

tff(c_1799,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1266,c_1796])).

tff(c_1388,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_subset_1(A_85,B_86,C_87) = k4_xboole_0(B_86,C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1391,plain,(
    ! [C_87] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_87) = k4_xboole_0('#skF_2',C_87) ),
    inference(resolution,[status(thm)],[c_28,c_1388])).

tff(c_2146,plain,(
    ! [A_117,B_118] :
      ( k7_subset_1(u1_struct_0(A_117),B_118,k2_tops_1(A_117,B_118)) = k1_tops_1(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2150,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2146])).

tff(c_2154,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1799,c_1391,c_2150])).

tff(c_2164,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_12])).

tff(c_2172,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2164])).

tff(c_1276,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1394,plain,(
    ! [A_88,B_89] : r1_tarski(k3_xboole_0(A_88,B_89),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_6])).

tff(c_1413,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1394])).

tff(c_2196,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2172,c_1413])).

tff(c_2209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1265,c_2196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:05:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.55  
% 3.45/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.55  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.45/1.55  
% 3.45/1.55  %Foreground sorts:
% 3.45/1.55  
% 3.45/1.55  
% 3.45/1.55  %Background operators:
% 3.45/1.55  
% 3.45/1.55  
% 3.45/1.55  %Foreground operators:
% 3.45/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.45/1.55  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.45/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.55  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.45/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.45/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.45/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.55  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.45/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.45/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.45/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.55  
% 3.45/1.56  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.45/1.56  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.45/1.56  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.45/1.56  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.45/1.56  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.45/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.45/1.56  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.45/1.56  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.45/1.56  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.45/1.56  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 3.45/1.56  tff(c_32, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.56  tff(c_128, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.45/1.56  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.56  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.56  tff(c_591, plain, (![B_62, A_63]: (v2_tops_1(B_62, A_63) | k1_tops_1(A_63, B_62)!=k1_xboole_0 | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.56  tff(c_594, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_591])).
% 3.45/1.56  tff(c_597, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_594])).
% 3.45/1.56  tff(c_598, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_128, c_597])).
% 3.45/1.56  tff(c_147, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.56  tff(c_49, plain, (![A_31, B_32]: (r1_tarski(k4_xboole_0(A_31, B_32), A_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.56  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.45/1.56  tff(c_57, plain, (![B_32]: (k4_xboole_0(k1_xboole_0, B_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_49, c_10])).
% 3.45/1.56  tff(c_184, plain, (![B_45]: (k3_xboole_0(k1_xboole_0, B_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_57])).
% 3.45/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.45/1.56  tff(c_196, plain, (![B_45]: (k3_xboole_0(B_45, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_2])).
% 3.45/1.56  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.56  tff(c_176, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_147])).
% 3.45/1.56  tff(c_374, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_176])).
% 3.45/1.56  tff(c_38, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.45/1.56  tff(c_138, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_128, c_38])).
% 3.45/1.56  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_142, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_138, c_4])).
% 3.45/1.56  tff(c_180, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.45/1.56  tff(c_183, plain, (![C_44]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_44)=k4_xboole_0('#skF_2', C_44))), inference(resolution, [status(thm)], [c_28, c_180])).
% 3.45/1.56  tff(c_1171, plain, (![A_78, B_79]: (k7_subset_1(u1_struct_0(A_78), B_79, k2_tops_1(A_78, B_79))=k1_tops_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.56  tff(c_1175, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1171])).
% 3.45/1.56  tff(c_1179, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_183, c_1175])).
% 3.45/1.56  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.56  tff(c_1189, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1179, c_12])).
% 3.45/1.56  tff(c_1197, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1189])).
% 3.45/1.56  tff(c_1212, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1197, c_12])).
% 3.45/1.56  tff(c_1220, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_374, c_1212])).
% 3.45/1.56  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.56  tff(c_119, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.56  tff(c_127, plain, (![A_5, B_6]: (k3_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k4_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_6, c_119])).
% 3.45/1.56  tff(c_1186, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1179, c_127])).
% 3.45/1.56  tff(c_1196, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_2, c_1186])).
% 3.45/1.56  tff(c_1263, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1196])).
% 3.45/1.56  tff(c_1264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_598, c_1263])).
% 3.45/1.56  tff(c_1265, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 3.45/1.56  tff(c_1266, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.45/1.56  tff(c_1793, plain, (![A_107, B_108]: (k1_tops_1(A_107, B_108)=k1_xboole_0 | ~v2_tops_1(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.56  tff(c_1796, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1793])).
% 3.45/1.56  tff(c_1799, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1266, c_1796])).
% 3.45/1.56  tff(c_1388, plain, (![A_85, B_86, C_87]: (k7_subset_1(A_85, B_86, C_87)=k4_xboole_0(B_86, C_87) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.45/1.56  tff(c_1391, plain, (![C_87]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_87)=k4_xboole_0('#skF_2', C_87))), inference(resolution, [status(thm)], [c_28, c_1388])).
% 3.45/1.56  tff(c_2146, plain, (![A_117, B_118]: (k7_subset_1(u1_struct_0(A_117), B_118, k2_tops_1(A_117, B_118))=k1_tops_1(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.56  tff(c_2150, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2146])).
% 3.45/1.56  tff(c_2154, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1799, c_1391, c_2150])).
% 3.45/1.56  tff(c_2164, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2154, c_12])).
% 3.45/1.56  tff(c_2172, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2164])).
% 3.45/1.56  tff(c_1276, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.56  tff(c_1394, plain, (![A_88, B_89]: (r1_tarski(k3_xboole_0(A_88, B_89), A_88))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_6])).
% 3.45/1.56  tff(c_1413, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1394])).
% 3.45/1.56  tff(c_2196, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2172, c_1413])).
% 3.45/1.56  tff(c_2209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1265, c_2196])).
% 3.45/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.56  
% 3.45/1.56  Inference rules
% 3.45/1.56  ----------------------
% 3.45/1.56  #Ref     : 0
% 3.45/1.56  #Sup     : 528
% 3.45/1.56  #Fact    : 0
% 3.45/1.56  #Define  : 0
% 3.45/1.56  #Split   : 1
% 3.45/1.56  #Chain   : 0
% 3.45/1.56  #Close   : 0
% 3.45/1.56  
% 3.45/1.56  Ordering : KBO
% 3.45/1.56  
% 3.45/1.56  Simplification rules
% 3.45/1.56  ----------------------
% 3.45/1.56  #Subsume      : 7
% 3.45/1.56  #Demod        : 554
% 3.45/1.56  #Tautology    : 412
% 3.45/1.56  #SimpNegUnit  : 6
% 3.45/1.56  #BackRed      : 0
% 3.45/1.56  
% 3.45/1.56  #Partial instantiations: 0
% 3.45/1.56  #Strategies tried      : 1
% 3.45/1.56  
% 3.45/1.56  Timing (in seconds)
% 3.45/1.56  ----------------------
% 3.45/1.57  Preprocessing        : 0.31
% 3.45/1.57  Parsing              : 0.17
% 3.45/1.57  CNF conversion       : 0.02
% 3.45/1.57  Main loop            : 0.49
% 3.45/1.57  Inferencing          : 0.16
% 3.45/1.57  Reduction            : 0.21
% 3.45/1.57  Demodulation         : 0.18
% 3.45/1.57  BG Simplification    : 0.02
% 3.45/1.57  Subsumption          : 0.06
% 3.45/1.57  Abstraction          : 0.03
% 3.45/1.57  MUC search           : 0.00
% 3.45/1.57  Cooper               : 0.00
% 3.45/1.57  Total                : 0.83
% 3.45/1.57  Index Insertion      : 0.00
% 3.45/1.57  Index Deletion       : 0.00
% 3.45/1.57  Index Matching       : 0.00
% 3.45/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
