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
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 263 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 579 expanded)
%              Number of equality atoms :   55 ( 152 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3301,plain,(
    ! [A_208,B_209,C_210] :
      ( k7_subset_1(A_208,B_209,C_210) = k4_xboole_0(B_209,C_210)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3310,plain,(
    ! [C_210] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_210) = k4_xboole_0('#skF_2',C_210) ),
    inference(resolution,[status(thm)],[c_40,c_3301])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_99,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_174,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1181,plain,(
    ! [B_110,A_111] :
      ( v4_pre_topc(B_110,A_111)
      | k2_pre_topc(A_111,B_110) != B_110
      | ~ v2_pre_topc(A_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1192,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1181])).

tff(c_1197,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1192])).

tff(c_1198,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_1197])).

tff(c_89,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_89])).

tff(c_1455,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(u1_struct_0(A_116),B_117,k2_tops_1(A_116,B_117)) = k2_pre_topc(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1463,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1455])).

tff(c_1468,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1463])).

tff(c_531,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_541,plain,(
    ! [C_85] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_85) = k4_xboole_0('#skF_2',C_85) ),
    inference(resolution,[status(thm)],[c_40,c_531])).

tff(c_547,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_99])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_142,plain,(
    ! [A_1,B_52] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_52)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_571,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_142])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_568,plain,(
    ! [B_6] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_6)
      | ~ r1_tarski('#skF_2',B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_10])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_801,plain,(
    ! [A_97,B_98,C_99] :
      ( k4_subset_1(A_97,B_98,C_99) = k2_xboole_0(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2426,plain,(
    ! [B_144,B_145,A_146] :
      ( k4_subset_1(B_144,B_145,A_146) = k2_xboole_0(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(B_144))
      | ~ r1_tarski(A_146,B_144) ) ),
    inference(resolution,[status(thm)],[c_28,c_801])).

tff(c_2549,plain,(
    ! [A_152] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_152) = k2_xboole_0('#skF_2',A_152)
      | ~ r1_tarski(A_152,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_2426])).

tff(c_2577,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_568,c_2549])).

tff(c_2620,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1468,c_571,c_2577])).

tff(c_2622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1198,c_2620])).

tff(c_2623,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_2623])).

tff(c_2871,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2947,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_46])).

tff(c_3311,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3310,c_2947])).

tff(c_3690,plain,(
    ! [A_231,B_232] :
      ( r1_tarski(k2_tops_1(A_231,B_232),B_232)
      | ~ v4_pre_topc(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3698,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3690])).

tff(c_3703,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2871,c_3698])).

tff(c_3094,plain,(
    ! [A_198,B_199] :
      ( k4_xboole_0(A_198,B_199) = k3_subset_1(A_198,B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3105,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_28,c_3094])).

tff(c_3712,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3703,c_3105])).

tff(c_4389,plain,(
    ! [A_255,B_256] :
      ( k7_subset_1(u1_struct_0(A_255),B_256,k2_tops_1(A_255,B_256)) = k1_tops_1(A_255,B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4397,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_4389])).

tff(c_4402,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3712,c_3310,c_4397])).

tff(c_3133,plain,(
    ! [A_200,B_201] :
      ( k3_subset_1(A_200,k3_subset_1(A_200,B_201)) = B_201
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3141,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_28,c_3133])).

tff(c_4410,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4402,c_3141])).

tff(c_4420,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3703,c_4410])).

tff(c_4406,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4402,c_3712])).

tff(c_3162,plain,(
    ! [B_202,A_203] :
      ( k4_xboole_0(B_202,A_203) = k3_subset_1(B_202,A_203)
      | ~ r1_tarski(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_28,c_3094])).

tff(c_3187,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_subset_1(A_10,k4_xboole_0(A_10,B_11)) ),
    inference(resolution,[status(thm)],[c_14,c_3162])).

tff(c_4548,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4406,c_3187])).

tff(c_4573,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4406,c_4548])).

tff(c_5514,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4420,c_4573])).

tff(c_5515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3311,c_5514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.06  
% 5.31/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.06  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.31/2.06  
% 5.31/2.06  %Foreground sorts:
% 5.31/2.06  
% 5.31/2.06  
% 5.31/2.06  %Background operators:
% 5.31/2.06  
% 5.31/2.06  
% 5.31/2.06  %Foreground operators:
% 5.31/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.31/2.06  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.31/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.31/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/2.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.31/2.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.31/2.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.31/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.31/2.06  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.31/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.31/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/2.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.31/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.31/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.31/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.31/2.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.31/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/2.06  
% 5.66/2.07  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.66/2.07  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.66/2.07  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.66/2.07  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.66/2.07  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.66/2.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.66/2.07  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.66/2.07  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.66/2.07  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 5.66/2.07  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.66/2.07  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.66/2.07  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.66/2.07  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.66/2.07  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.66/2.07  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.66/2.07  tff(c_3301, plain, (![A_208, B_209, C_210]: (k7_subset_1(A_208, B_209, C_210)=k4_xboole_0(B_209, C_210) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.66/2.07  tff(c_3310, plain, (![C_210]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_210)=k4_xboole_0('#skF_2', C_210))), inference(resolution, [status(thm)], [c_40, c_3301])).
% 5.66/2.07  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.66/2.07  tff(c_99, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.66/2.07  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.66/2.07  tff(c_174, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.66/2.07  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.66/2.07  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.66/2.07  tff(c_1181, plain, (![B_110, A_111]: (v4_pre_topc(B_110, A_111) | k2_pre_topc(A_111, B_110)!=B_110 | ~v2_pre_topc(A_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.66/2.07  tff(c_1192, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1181])).
% 5.66/2.07  tff(c_1197, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1192])).
% 5.66/2.07  tff(c_1198, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_174, c_1197])).
% 5.66/2.07  tff(c_89, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.66/2.08  tff(c_93, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_89])).
% 5.66/2.08  tff(c_1455, plain, (![A_116, B_117]: (k4_subset_1(u1_struct_0(A_116), B_117, k2_tops_1(A_116, B_117))=k2_pre_topc(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.66/2.08  tff(c_1463, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1455])).
% 5.66/2.08  tff(c_1468, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1463])).
% 5.66/2.08  tff(c_531, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.66/2.08  tff(c_541, plain, (![C_85]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_85)=k4_xboole_0('#skF_2', C_85))), inference(resolution, [status(thm)], [c_40, c_531])).
% 5.66/2.08  tff(c_547, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_541, c_99])).
% 5.66/2.08  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.66/2.08  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.66/2.08  tff(c_100, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.66/2.08  tff(c_122, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), A_51)=A_51)), inference(resolution, [status(thm)], [c_14, c_100])).
% 5.66/2.08  tff(c_142, plain, (![A_1, B_52]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_52))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 5.66/2.08  tff(c_571, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_547, c_142])).
% 5.66/2.08  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.66/2.08  tff(c_568, plain, (![B_6]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_6) | ~r1_tarski('#skF_2', B_6))), inference(superposition, [status(thm), theory('equality')], [c_547, c_10])).
% 5.66/2.08  tff(c_28, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.66/2.08  tff(c_801, plain, (![A_97, B_98, C_99]: (k4_subset_1(A_97, B_98, C_99)=k2_xboole_0(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.66/2.08  tff(c_2426, plain, (![B_144, B_145, A_146]: (k4_subset_1(B_144, B_145, A_146)=k2_xboole_0(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(B_144)) | ~r1_tarski(A_146, B_144))), inference(resolution, [status(thm)], [c_28, c_801])).
% 5.66/2.08  tff(c_2549, plain, (![A_152]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_152)=k2_xboole_0('#skF_2', A_152) | ~r1_tarski(A_152, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_2426])).
% 5.66/2.08  tff(c_2577, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_568, c_2549])).
% 5.66/2.08  tff(c_2620, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1468, c_571, c_2577])).
% 5.66/2.08  tff(c_2622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1198, c_2620])).
% 5.66/2.08  tff(c_2623, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.66/2.08  tff(c_2870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_2623])).
% 5.66/2.08  tff(c_2871, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.66/2.08  tff(c_2947, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_46])).
% 5.66/2.08  tff(c_3311, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3310, c_2947])).
% 5.66/2.08  tff(c_3690, plain, (![A_231, B_232]: (r1_tarski(k2_tops_1(A_231, B_232), B_232) | ~v4_pre_topc(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.66/2.08  tff(c_3698, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3690])).
% 5.66/2.08  tff(c_3703, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2871, c_3698])).
% 5.66/2.08  tff(c_3094, plain, (![A_198, B_199]: (k4_xboole_0(A_198, B_199)=k3_subset_1(A_198, B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.08  tff(c_3105, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_28, c_3094])).
% 5.66/2.08  tff(c_3712, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3703, c_3105])).
% 5.66/2.08  tff(c_4389, plain, (![A_255, B_256]: (k7_subset_1(u1_struct_0(A_255), B_256, k2_tops_1(A_255, B_256))=k1_tops_1(A_255, B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.66/2.08  tff(c_4397, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_4389])).
% 5.66/2.08  tff(c_4402, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3712, c_3310, c_4397])).
% 5.66/2.08  tff(c_3133, plain, (![A_200, B_201]: (k3_subset_1(A_200, k3_subset_1(A_200, B_201))=B_201 | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.66/2.08  tff(c_3141, plain, (![B_25, A_24]: (k3_subset_1(B_25, k3_subset_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_28, c_3133])).
% 5.66/2.08  tff(c_4410, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4402, c_3141])).
% 5.66/2.08  tff(c_4420, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3703, c_4410])).
% 5.66/2.08  tff(c_4406, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4402, c_3712])).
% 5.66/2.08  tff(c_3162, plain, (![B_202, A_203]: (k4_xboole_0(B_202, A_203)=k3_subset_1(B_202, A_203) | ~r1_tarski(A_203, B_202))), inference(resolution, [status(thm)], [c_28, c_3094])).
% 5.66/2.08  tff(c_3187, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_subset_1(A_10, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_14, c_3162])).
% 5.66/2.08  tff(c_4548, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4406, c_3187])).
% 5.66/2.08  tff(c_4573, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4406, c_4548])).
% 5.66/2.08  tff(c_5514, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4420, c_4573])).
% 5.66/2.08  tff(c_5515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3311, c_5514])).
% 5.66/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.08  
% 5.66/2.08  Inference rules
% 5.66/2.08  ----------------------
% 5.66/2.08  #Ref     : 0
% 5.66/2.08  #Sup     : 1318
% 5.66/2.08  #Fact    : 0
% 5.66/2.08  #Define  : 0
% 5.66/2.08  #Split   : 9
% 5.66/2.08  #Chain   : 0
% 5.66/2.08  #Close   : 0
% 5.66/2.08  
% 5.66/2.08  Ordering : KBO
% 5.66/2.08  
% 5.66/2.08  Simplification rules
% 5.66/2.08  ----------------------
% 5.66/2.08  #Subsume      : 109
% 5.66/2.08  #Demod        : 441
% 5.66/2.08  #Tautology    : 509
% 5.66/2.08  #SimpNegUnit  : 4
% 5.66/2.08  #BackRed      : 6
% 5.66/2.08  
% 5.66/2.08  #Partial instantiations: 0
% 5.66/2.08  #Strategies tried      : 1
% 5.66/2.08  
% 5.66/2.08  Timing (in seconds)
% 5.66/2.08  ----------------------
% 5.66/2.08  Preprocessing        : 0.34
% 5.66/2.08  Parsing              : 0.18
% 5.66/2.08  CNF conversion       : 0.02
% 5.66/2.08  Main loop            : 0.97
% 5.66/2.08  Inferencing          : 0.32
% 5.66/2.08  Reduction            : 0.33
% 5.66/2.08  Demodulation         : 0.25
% 5.66/2.08  BG Simplification    : 0.04
% 5.66/2.08  Subsumption          : 0.18
% 5.66/2.08  Abstraction          : 0.05
% 5.66/2.08  MUC search           : 0.00
% 5.66/2.08  Cooper               : 0.00
% 5.66/2.08  Total                : 1.35
% 5.66/2.08  Index Insertion      : 0.00
% 5.66/2.08  Index Deletion       : 0.00
% 5.66/2.08  Index Matching       : 0.00
% 5.66/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
