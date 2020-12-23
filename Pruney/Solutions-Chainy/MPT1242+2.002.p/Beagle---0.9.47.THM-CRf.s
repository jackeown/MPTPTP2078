%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:49 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 170 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  131 ( 356 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
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
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_164,plain,(
    ! [A_65,B_66] :
      ( k3_subset_1(A_65,k3_subset_1(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_176,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_40,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    ! [A_25,B_27] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_25),B_27),A_25)
      | ~ v3_pre_topc(B_27,A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_114])).

tff(c_135,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_174,plain,(
    ! [A_13] : k3_subset_1(A_13,k3_subset_1(A_13,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_164])).

tff(c_180,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_174])).

tff(c_488,plain,(
    ! [A_90,C_91,B_92] :
      ( r1_tarski(k3_subset_1(A_90,C_91),B_92)
      | ~ r1_tarski(k3_subset_1(A_90,B_92),C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_496,plain,(
    ! [A_13,C_91] :
      ( r1_tarski(k3_subset_1(A_13,C_91),A_13)
      | ~ r1_tarski(k1_xboole_0,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(A_13,k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_488])).

tff(c_503,plain,(
    ! [A_13,C_91] :
      ( r1_tarski(k3_subset_1(A_13,C_91),A_13)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2,c_496])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_498,plain,(
    ! [A_13,C_91] :
      ( r1_tarski(k3_subset_1(A_13,C_91),k1_xboole_0)
      | ~ r1_tarski(A_13,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_488])).

tff(c_552,plain,(
    ! [A_96,C_97] :
      ( r1_tarski(k3_subset_1(A_96,C_97),k1_xboole_0)
      | ~ r1_tarski(A_96,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_498])).

tff(c_566,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_552])).

tff(c_703,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_707,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_703])).

tff(c_710,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_503,c_707])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_710])).

tff(c_716,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_26,plain,(
    ! [A_19,B_21] :
      ( k2_pre_topc(A_19,B_21) = B_21
      | ~ v4_pre_topc(B_21,A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_722,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_716,c_26])).

tff(c_738,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_722])).

tff(c_1343,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_1346,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1343])).

tff(c_1350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_1346])).

tff(c_1351,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_28,plain,(
    ! [A_22,B_24] :
      ( k3_subset_1(u1_struct_0(A_22),k2_pre_topc(A_22,k3_subset_1(u1_struct_0(A_22),B_24))) = k1_tops_1(A_22,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1368,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_28])).

tff(c_1377,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_176,c_1368])).

tff(c_34,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1382,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_2',k1_tops_1('#skF_1',C_34))
      | ~ r1_tarski('#skF_2',C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_34])).

tff(c_1394,plain,(
    ! [C_126] :
      ( r1_tarski('#skF_2',k1_tops_1('#skF_1',C_126))
      | ~ r1_tarski('#skF_2',C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1382])).

tff(c_1410,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1394])).

tff(c_1427,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1410])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.59  
% 3.48/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.59  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.59  
% 3.48/1.59  %Foreground sorts:
% 3.48/1.59  
% 3.48/1.59  
% 3.48/1.59  %Background operators:
% 3.48/1.59  
% 3.48/1.59  
% 3.48/1.59  %Foreground operators:
% 3.48/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.48/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.48/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.48/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.48/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.48/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.59  
% 3.48/1.60  tff(f_120, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.48/1.60  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.48/1.60  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 3.48/1.60  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.48/1.60  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.48/1.60  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.48/1.60  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.48/1.60  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.48/1.60  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.48/1.60  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 3.48/1.60  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.60  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.48/1.60  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.48/1.60  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.48/1.60  tff(c_36, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.60  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.60  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.60  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.60  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.60  tff(c_164, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_subset_1(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.60  tff(c_176, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_44, c_164])).
% 3.48/1.60  tff(c_40, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.48/1.60  tff(c_32, plain, (![A_25, B_27]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_25), B_27), A_25) | ~v3_pre_topc(B_27, A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.48/1.60  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.60  tff(c_10, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.60  tff(c_47, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 3.48/1.60  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.60  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.60  tff(c_16, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.48/1.60  tff(c_114, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.60  tff(c_129, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_114])).
% 3.48/1.60  tff(c_135, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_129])).
% 3.48/1.60  tff(c_174, plain, (![A_13]: (k3_subset_1(A_13, k3_subset_1(A_13, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_164])).
% 3.48/1.60  tff(c_180, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_174])).
% 3.48/1.60  tff(c_488, plain, (![A_90, C_91, B_92]: (r1_tarski(k3_subset_1(A_90, C_91), B_92) | ~r1_tarski(k3_subset_1(A_90, B_92), C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_90)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.60  tff(c_496, plain, (![A_13, C_91]: (r1_tarski(k3_subset_1(A_13, C_91), A_13) | ~r1_tarski(k1_xboole_0, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_13)) | ~m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_488])).
% 3.48/1.60  tff(c_503, plain, (![A_13, C_91]: (r1_tarski(k3_subset_1(A_13, C_91), A_13) | ~m1_subset_1(C_91, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_2, c_496])).
% 3.48/1.60  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.48/1.60  tff(c_498, plain, (![A_13, C_91]: (r1_tarski(k3_subset_1(A_13, C_91), k1_xboole_0) | ~r1_tarski(A_13, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_13)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_488])).
% 3.48/1.60  tff(c_552, plain, (![A_96, C_97]: (r1_tarski(k3_subset_1(A_96, C_97), k1_xboole_0) | ~r1_tarski(A_96, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(A_96)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_498])).
% 3.48/1.60  tff(c_566, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_176, c_552])).
% 3.48/1.60  tff(c_703, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_566])).
% 3.48/1.60  tff(c_707, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_703])).
% 3.48/1.60  tff(c_710, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_503, c_707])).
% 3.48/1.60  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_710])).
% 3.48/1.60  tff(c_716, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_566])).
% 3.48/1.60  tff(c_26, plain, (![A_19, B_21]: (k2_pre_topc(A_19, B_21)=B_21 | ~v4_pre_topc(B_21, A_19) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.48/1.60  tff(c_722, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_716, c_26])).
% 3.48/1.60  tff(c_738, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_722])).
% 3.48/1.60  tff(c_1343, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_738])).
% 3.48/1.60  tff(c_1346, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1343])).
% 3.48/1.60  tff(c_1350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_1346])).
% 3.48/1.60  tff(c_1351, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_738])).
% 3.48/1.60  tff(c_28, plain, (![A_22, B_24]: (k3_subset_1(u1_struct_0(A_22), k2_pre_topc(A_22, k3_subset_1(u1_struct_0(A_22), B_24)))=k1_tops_1(A_22, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.48/1.60  tff(c_1368, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1351, c_28])).
% 3.48/1.60  tff(c_1377, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_176, c_1368])).
% 3.48/1.60  tff(c_34, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.48/1.60  tff(c_1382, plain, (![C_34]: (r1_tarski('#skF_2', k1_tops_1('#skF_1', C_34)) | ~r1_tarski('#skF_2', C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1377, c_34])).
% 3.48/1.60  tff(c_1394, plain, (![C_126]: (r1_tarski('#skF_2', k1_tops_1('#skF_1', C_126)) | ~r1_tarski('#skF_2', C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1382])).
% 3.48/1.60  tff(c_1410, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1394])).
% 3.48/1.60  tff(c_1427, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1410])).
% 3.48/1.60  tff(c_1429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1427])).
% 3.48/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  Inference rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Ref     : 0
% 3.48/1.60  #Sup     : 305
% 3.48/1.60  #Fact    : 0
% 3.48/1.60  #Define  : 0
% 3.48/1.60  #Split   : 12
% 3.48/1.60  #Chain   : 0
% 3.48/1.60  #Close   : 0
% 3.48/1.60  
% 3.48/1.60  Ordering : KBO
% 3.48/1.60  
% 3.48/1.60  Simplification rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Subsume      : 25
% 3.48/1.60  #Demod        : 232
% 3.48/1.60  #Tautology    : 112
% 3.48/1.60  #SimpNegUnit  : 11
% 3.48/1.60  #BackRed      : 1
% 3.48/1.60  
% 3.48/1.60  #Partial instantiations: 0
% 3.48/1.60  #Strategies tried      : 1
% 3.48/1.60  
% 3.48/1.60  Timing (in seconds)
% 3.48/1.60  ----------------------
% 3.48/1.61  Preprocessing        : 0.32
% 3.48/1.61  Parsing              : 0.18
% 3.48/1.61  CNF conversion       : 0.02
% 3.48/1.61  Main loop            : 0.50
% 3.48/1.61  Inferencing          : 0.17
% 3.48/1.61  Reduction            : 0.18
% 3.48/1.61  Demodulation         : 0.13
% 3.48/1.61  BG Simplification    : 0.02
% 3.48/1.61  Subsumption          : 0.09
% 3.48/1.61  Abstraction          : 0.03
% 3.48/1.61  MUC search           : 0.00
% 3.48/1.61  Cooper               : 0.00
% 3.48/1.61  Total                : 0.86
% 3.48/1.61  Index Insertion      : 0.00
% 3.48/1.61  Index Deletion       : 0.00
% 3.48/1.61  Index Matching       : 0.00
% 3.48/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
