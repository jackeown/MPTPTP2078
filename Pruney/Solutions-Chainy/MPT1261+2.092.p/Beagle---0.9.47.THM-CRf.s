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
% DateTime   : Thu Dec  3 10:21:25 EST 2020

% Result     : Theorem 14.78s
% Output     : CNFRefutation 14.78s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 244 expanded)
%              Number of leaves         :   49 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 436 expanded)
%              Number of equality atoms :   75 ( 144 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_34409,plain,(
    ! [A_629,B_630,C_631] :
      ( k7_subset_1(A_629,B_630,C_631) = k4_xboole_0(B_630,C_631)
      | ~ m1_subset_1(B_630,k1_zfmisc_1(A_629)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34422,plain,(
    ! [C_631] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_631) = k4_xboole_0('#skF_2',C_631) ),
    inference(resolution,[status(thm)],[c_64,c_34409])).

tff(c_70,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_146,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3715,plain,(
    ! [B_247,A_248] :
      ( v4_pre_topc(B_247,A_248)
      | k2_pre_topc(A_248,B_247) != B_247
      | ~ v2_pre_topc(A_248)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3726,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_3715])).

tff(c_3739,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_3726])).

tff(c_3740,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_3739])).

tff(c_4108,plain,(
    ! [A_259,B_260] :
      ( k4_subset_1(u1_struct_0(A_259),B_260,k2_tops_1(A_259,B_260)) = k2_pre_topc(A_259,B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4116,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_4108])).

tff(c_4127,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4116])).

tff(c_76,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_270,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_76])).

tff(c_2326,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_subset_1(A_194,B_195,C_196) = k4_xboole_0(B_195,C_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2455,plain,(
    ! [C_204] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_204) = k4_xboole_0('#skF_2',C_204) ),
    inference(resolution,[status(thm)],[c_64,c_2326])).

tff(c_2467,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_2455])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_220,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(A_79,B_80) = B_80
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    ! [A_81,B_82] : k2_xboole_0(k4_xboole_0(A_81,B_82),A_81) = A_81 ),
    inference(resolution,[status(thm)],[c_14,c_220])).

tff(c_249,plain,(
    ! [A_1,B_82] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_82)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_2747,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2467,c_249])).

tff(c_316,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_326,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_316])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_338,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_326,c_8])).

tff(c_635,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(A_107,C_108)
      | ~ r1_tarski(B_109,C_108)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1185,plain,(
    ! [A_147,A_148,B_149] :
      ( r1_tarski(A_147,A_148)
      | ~ r1_tarski(A_147,k4_xboole_0(A_148,B_149)) ) ),
    inference(resolution,[status(thm)],[c_14,c_635])).

tff(c_1232,plain,(
    ! [A_148,B_149,B_14] : r1_tarski(k4_xboole_0(k4_xboole_0(A_148,B_149),B_14),A_148) ),
    inference(resolution,[status(thm)],[c_14,c_1185])).

tff(c_1500,plain,(
    ! [A_165,B_166,C_167] :
      ( r1_tarski(A_165,k2_xboole_0(B_166,C_167))
      | ~ r1_tarski(k4_xboole_0(A_165,B_166),C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1787,plain,(
    ! [A_174,B_175,B_176] : r1_tarski(k4_xboole_0(A_174,B_175),k2_xboole_0(B_176,A_174)) ),
    inference(resolution,[status(thm)],[c_1232,c_1500])).

tff(c_2370,plain,(
    ! [B_201,B_202,A_203] : r1_tarski(k4_xboole_0(B_201,B_202),k2_xboole_0(B_201,A_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1787])).

tff(c_2411,plain,(
    ! [B_202] : r1_tarski(k4_xboole_0('#skF_2',B_202),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_2370])).

tff(c_2714,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2467,c_2411])).

tff(c_46,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2928,plain,(
    ! [A_216,B_217,C_218] :
      ( k4_subset_1(A_216,B_217,C_218) = k2_xboole_0(B_217,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_31579,plain,(
    ! [B_525,B_526,A_527] :
      ( k4_subset_1(B_525,B_526,A_527) = k2_xboole_0(B_526,A_527)
      | ~ m1_subset_1(B_526,k1_zfmisc_1(B_525))
      | ~ r1_tarski(A_527,B_525) ) ),
    inference(resolution,[status(thm)],[c_46,c_2928])).

tff(c_32421,plain,(
    ! [A_534] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_534) = k2_xboole_0('#skF_2',A_534)
      | ~ r1_tarski(A_534,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_64,c_31579])).

tff(c_32504,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2714,c_32421])).

tff(c_32605,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4127,c_2747,c_32504])).

tff(c_32607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3740,c_32605])).

tff(c_32608,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_34453,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34422,c_32608])).

tff(c_32609,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_34759,plain,(
    ! [A_649,B_650] :
      ( r1_tarski(k2_tops_1(A_649,B_650),B_650)
      | ~ v4_pre_topc(B_650,A_649)
      | ~ m1_subset_1(B_650,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ l1_pre_topc(A_649) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34767,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_34759])).

tff(c_34778,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32609,c_34767])).

tff(c_36029,plain,(
    ! [A_703,B_704] :
      ( k7_subset_1(u1_struct_0(A_703),B_704,k2_tops_1(A_703,B_704)) = k1_tops_1(A_703,B_704)
      | ~ m1_subset_1(B_704,k1_zfmisc_1(u1_struct_0(A_703)))
      | ~ l1_pre_topc(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36037,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_36029])).

tff(c_36048,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_34422,c_36037])).

tff(c_33127,plain,(
    ! [A_574,B_575] :
      ( k4_xboole_0(A_574,B_575) = k3_subset_1(A_574,B_575)
      | ~ m1_subset_1(B_575,k1_zfmisc_1(A_574)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38206,plain,(
    ! [B_762,A_763] :
      ( k4_xboole_0(B_762,A_763) = k3_subset_1(B_762,A_763)
      | ~ r1_tarski(A_763,B_762) ) ),
    inference(resolution,[status(thm)],[c_46,c_33127])).

tff(c_38341,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34778,c_38206])).

tff(c_38426,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36048,c_38341])).

tff(c_33540,plain,(
    ! [A_592,B_593] :
      ( k3_subset_1(A_592,k3_subset_1(A_592,B_593)) = B_593
      | ~ m1_subset_1(B_593,k1_zfmisc_1(A_592)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_33549,plain,(
    ! [B_45,A_44] :
      ( k3_subset_1(B_45,k3_subset_1(B_45,A_44)) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_46,c_33540])).

tff(c_38831,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38426,c_33549])).

tff(c_38841,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34778,c_38831])).

tff(c_99,plain,(
    ! [B_74,A_75] : k2_xboole_0(B_74,A_75) = k2_xboole_0(A_75,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_75] : k2_xboole_0(k1_xboole_0,A_75) = A_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_32851,plain,(
    ! [A_556,B_557] : k2_xboole_0(A_556,k4_xboole_0(B_557,A_556)) = k2_xboole_0(A_556,B_557) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32862,plain,(
    ! [B_557] : k4_xboole_0(B_557,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_557) ),
    inference(superposition,[status(thm),theory(equality)],[c_32851,c_115])).

tff(c_32879,plain,(
    ! [B_557] : k4_xboole_0(B_557,k1_xboole_0) = B_557 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_32862])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34521,plain,(
    ! [A_639,B_640] :
      ( r1_tarski(k1_tops_1(A_639,B_640),B_640)
      | ~ m1_subset_1(B_640,k1_zfmisc_1(u1_struct_0(A_639)))
      | ~ l1_pre_topc(A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34529,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_34521])).

tff(c_34540,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_34529])).

tff(c_33812,plain,(
    ! [A_602,B_603,C_604] :
      ( r1_tarski(k4_xboole_0(A_602,B_603),C_604)
      | ~ r1_tarski(A_602,k2_xboole_0(B_603,C_604)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44198,plain,(
    ! [A_841,B_842,C_843] :
      ( k2_xboole_0(k4_xboole_0(A_841,B_842),C_843) = C_843
      | ~ r1_tarski(A_841,k2_xboole_0(B_842,C_843)) ) ),
    inference(resolution,[status(thm)],[c_33812,c_8])).

tff(c_44470,plain,(
    ! [A_841,A_9] :
      ( k2_xboole_0(k4_xboole_0(A_841,A_9),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_841,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44198])).

tff(c_44552,plain,(
    ! [A_844,A_845] :
      ( k4_xboole_0(A_844,A_845) = k1_xboole_0
      | ~ r1_tarski(A_844,A_845) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_2,c_44470])).

tff(c_44798,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34540,c_44552])).

tff(c_22,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44966,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44798,c_22])).

tff(c_45000,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32879,c_4,c_44966])).

tff(c_38380,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_subset_1(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(resolution,[status(thm)],[c_14,c_38206])).

tff(c_38560,plain,(
    ! [A_767,B_768] : k3_subset_1(A_767,k4_xboole_0(A_767,B_768)) = k3_xboole_0(A_767,B_768) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_38380])).

tff(c_38566,plain,(
    ! [A_767,B_768] :
      ( k3_subset_1(A_767,k3_xboole_0(A_767,B_768)) = k4_xboole_0(A_767,B_768)
      | ~ r1_tarski(k4_xboole_0(A_767,B_768),A_767) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38560,c_33549])).

tff(c_38596,plain,(
    ! [A_767,B_768] : k3_subset_1(A_767,k3_xboole_0(A_767,B_768)) = k4_xboole_0(A_767,B_768) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38566])).

tff(c_60030,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45000,c_38596])).

tff(c_60116,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38841,c_60030])).

tff(c_60118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34453,c_60116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.78/7.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.78/7.58  
% 14.78/7.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.78/7.58  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 14.78/7.58  
% 14.78/7.58  %Foreground sorts:
% 14.78/7.58  
% 14.78/7.58  
% 14.78/7.58  %Background operators:
% 14.78/7.58  
% 14.78/7.58  
% 14.78/7.58  %Foreground operators:
% 14.78/7.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.78/7.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.78/7.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.78/7.58  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.78/7.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.78/7.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.78/7.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.78/7.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.78/7.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.78/7.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.78/7.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.78/7.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.78/7.58  tff('#skF_2', type, '#skF_2': $i).
% 14.78/7.58  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.78/7.58  tff('#skF_1', type, '#skF_1': $i).
% 14.78/7.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.78/7.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.78/7.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.78/7.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.78/7.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.78/7.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.78/7.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.78/7.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.78/7.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.78/7.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.78/7.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.78/7.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.78/7.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.78/7.58  
% 14.78/7.60  tff(f_163, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 14.78/7.60  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.78/7.60  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 14.78/7.60  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 14.78/7.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.78/7.60  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.78/7.60  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.78/7.60  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.78/7.60  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.78/7.60  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 14.78/7.60  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.78/7.60  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 14.78/7.60  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 14.78/7.60  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 14.78/7.60  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.78/7.60  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.78/7.60  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.78/7.60  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.78/7.60  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 14.78/7.60  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 14.78/7.60  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.78/7.60  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.78/7.60  tff(c_34409, plain, (![A_629, B_630, C_631]: (k7_subset_1(A_629, B_630, C_631)=k4_xboole_0(B_630, C_631) | ~m1_subset_1(B_630, k1_zfmisc_1(A_629)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.78/7.60  tff(c_34422, plain, (![C_631]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_631)=k4_xboole_0('#skF_2', C_631))), inference(resolution, [status(thm)], [c_64, c_34409])).
% 14.78/7.60  tff(c_70, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.78/7.60  tff(c_146, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 14.78/7.60  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.78/7.60  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.78/7.60  tff(c_3715, plain, (![B_247, A_248]: (v4_pre_topc(B_247, A_248) | k2_pre_topc(A_248, B_247)!=B_247 | ~v2_pre_topc(A_248) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.78/7.60  tff(c_3726, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_3715])).
% 14.78/7.60  tff(c_3739, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_3726])).
% 14.78/7.60  tff(c_3740, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_146, c_3739])).
% 14.78/7.60  tff(c_4108, plain, (![A_259, B_260]: (k4_subset_1(u1_struct_0(A_259), B_260, k2_tops_1(A_259, B_260))=k2_pre_topc(A_259, B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.78/7.60  tff(c_4116, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_4108])).
% 14.78/7.60  tff(c_4127, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4116])).
% 14.78/7.60  tff(c_76, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 14.78/7.60  tff(c_270, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_146, c_76])).
% 14.78/7.60  tff(c_2326, plain, (![A_194, B_195, C_196]: (k7_subset_1(A_194, B_195, C_196)=k4_xboole_0(B_195, C_196) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.78/7.60  tff(c_2455, plain, (![C_204]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_204)=k4_xboole_0('#skF_2', C_204))), inference(resolution, [status(thm)], [c_64, c_2326])).
% 14.78/7.60  tff(c_2467, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_270, c_2455])).
% 14.78/7.60  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.78/7.60  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.78/7.60  tff(c_220, plain, (![A_79, B_80]: (k2_xboole_0(A_79, B_80)=B_80 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.78/7.60  tff(c_225, plain, (![A_81, B_82]: (k2_xboole_0(k4_xboole_0(A_81, B_82), A_81)=A_81)), inference(resolution, [status(thm)], [c_14, c_220])).
% 14.78/7.60  tff(c_249, plain, (![A_1, B_82]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_82))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_225])).
% 14.78/7.60  tff(c_2747, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2467, c_249])).
% 14.78/7.60  tff(c_316, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | ~m1_subset_1(A_88, k1_zfmisc_1(B_89)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.78/7.60  tff(c_326, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_316])).
% 14.78/7.60  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.78/7.60  tff(c_338, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_326, c_8])).
% 14.78/7.60  tff(c_635, plain, (![A_107, C_108, B_109]: (r1_tarski(A_107, C_108) | ~r1_tarski(B_109, C_108) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.78/7.60  tff(c_1185, plain, (![A_147, A_148, B_149]: (r1_tarski(A_147, A_148) | ~r1_tarski(A_147, k4_xboole_0(A_148, B_149)))), inference(resolution, [status(thm)], [c_14, c_635])).
% 14.78/7.60  tff(c_1232, plain, (![A_148, B_149, B_14]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_148, B_149), B_14), A_148))), inference(resolution, [status(thm)], [c_14, c_1185])).
% 14.78/7.60  tff(c_1500, plain, (![A_165, B_166, C_167]: (r1_tarski(A_165, k2_xboole_0(B_166, C_167)) | ~r1_tarski(k4_xboole_0(A_165, B_166), C_167))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.78/7.60  tff(c_1787, plain, (![A_174, B_175, B_176]: (r1_tarski(k4_xboole_0(A_174, B_175), k2_xboole_0(B_176, A_174)))), inference(resolution, [status(thm)], [c_1232, c_1500])).
% 14.78/7.60  tff(c_2370, plain, (![B_201, B_202, A_203]: (r1_tarski(k4_xboole_0(B_201, B_202), k2_xboole_0(B_201, A_203)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1787])).
% 14.78/7.60  tff(c_2411, plain, (![B_202]: (r1_tarski(k4_xboole_0('#skF_2', B_202), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_338, c_2370])).
% 14.78/7.60  tff(c_2714, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2467, c_2411])).
% 14.78/7.60  tff(c_46, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.78/7.60  tff(c_2928, plain, (![A_216, B_217, C_218]: (k4_subset_1(A_216, B_217, C_218)=k2_xboole_0(B_217, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.78/7.60  tff(c_31579, plain, (![B_525, B_526, A_527]: (k4_subset_1(B_525, B_526, A_527)=k2_xboole_0(B_526, A_527) | ~m1_subset_1(B_526, k1_zfmisc_1(B_525)) | ~r1_tarski(A_527, B_525))), inference(resolution, [status(thm)], [c_46, c_2928])).
% 14.78/7.60  tff(c_32421, plain, (![A_534]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_534)=k2_xboole_0('#skF_2', A_534) | ~r1_tarski(A_534, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_64, c_31579])).
% 14.78/7.60  tff(c_32504, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2714, c_32421])).
% 14.78/7.60  tff(c_32605, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4127, c_2747, c_32504])).
% 14.78/7.60  tff(c_32607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3740, c_32605])).
% 14.78/7.60  tff(c_32608, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 14.78/7.60  tff(c_34453, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34422, c_32608])).
% 14.78/7.60  tff(c_32609, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 14.78/7.60  tff(c_34759, plain, (![A_649, B_650]: (r1_tarski(k2_tops_1(A_649, B_650), B_650) | ~v4_pre_topc(B_650, A_649) | ~m1_subset_1(B_650, k1_zfmisc_1(u1_struct_0(A_649))) | ~l1_pre_topc(A_649))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.78/7.60  tff(c_34767, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_34759])).
% 14.78/7.60  tff(c_34778, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_32609, c_34767])).
% 14.78/7.60  tff(c_36029, plain, (![A_703, B_704]: (k7_subset_1(u1_struct_0(A_703), B_704, k2_tops_1(A_703, B_704))=k1_tops_1(A_703, B_704) | ~m1_subset_1(B_704, k1_zfmisc_1(u1_struct_0(A_703))) | ~l1_pre_topc(A_703))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.78/7.60  tff(c_36037, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_36029])).
% 14.78/7.60  tff(c_36048, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_34422, c_36037])).
% 14.78/7.60  tff(c_33127, plain, (![A_574, B_575]: (k4_xboole_0(A_574, B_575)=k3_subset_1(A_574, B_575) | ~m1_subset_1(B_575, k1_zfmisc_1(A_574)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.78/7.60  tff(c_38206, plain, (![B_762, A_763]: (k4_xboole_0(B_762, A_763)=k3_subset_1(B_762, A_763) | ~r1_tarski(A_763, B_762))), inference(resolution, [status(thm)], [c_46, c_33127])).
% 14.78/7.60  tff(c_38341, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34778, c_38206])).
% 14.78/7.60  tff(c_38426, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36048, c_38341])).
% 14.78/7.60  tff(c_33540, plain, (![A_592, B_593]: (k3_subset_1(A_592, k3_subset_1(A_592, B_593))=B_593 | ~m1_subset_1(B_593, k1_zfmisc_1(A_592)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.78/7.60  tff(c_33549, plain, (![B_45, A_44]: (k3_subset_1(B_45, k3_subset_1(B_45, A_44))=A_44 | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_46, c_33540])).
% 14.78/7.60  tff(c_38831, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38426, c_33549])).
% 14.78/7.60  tff(c_38841, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34778, c_38831])).
% 14.78/7.60  tff(c_99, plain, (![B_74, A_75]: (k2_xboole_0(B_74, A_75)=k2_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.78/7.60  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.78/7.60  tff(c_115, plain, (![A_75]: (k2_xboole_0(k1_xboole_0, A_75)=A_75)), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 14.78/7.60  tff(c_32851, plain, (![A_556, B_557]: (k2_xboole_0(A_556, k4_xboole_0(B_557, A_556))=k2_xboole_0(A_556, B_557))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.78/7.60  tff(c_32862, plain, (![B_557]: (k4_xboole_0(B_557, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_557))), inference(superposition, [status(thm), theory('equality')], [c_32851, c_115])).
% 14.78/7.60  tff(c_32879, plain, (![B_557]: (k4_xboole_0(B_557, k1_xboole_0)=B_557)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_32862])).
% 14.78/7.60  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.78/7.60  tff(c_34521, plain, (![A_639, B_640]: (r1_tarski(k1_tops_1(A_639, B_640), B_640) | ~m1_subset_1(B_640, k1_zfmisc_1(u1_struct_0(A_639))) | ~l1_pre_topc(A_639))), inference(cnfTransformation, [status(thm)], [f_121])).
% 14.78/7.60  tff(c_34529, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_34521])).
% 14.78/7.60  tff(c_34540, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_34529])).
% 14.78/7.60  tff(c_33812, plain, (![A_602, B_603, C_604]: (r1_tarski(k4_xboole_0(A_602, B_603), C_604) | ~r1_tarski(A_602, k2_xboole_0(B_603, C_604)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.78/7.60  tff(c_44198, plain, (![A_841, B_842, C_843]: (k2_xboole_0(k4_xboole_0(A_841, B_842), C_843)=C_843 | ~r1_tarski(A_841, k2_xboole_0(B_842, C_843)))), inference(resolution, [status(thm)], [c_33812, c_8])).
% 14.78/7.60  tff(c_44470, plain, (![A_841, A_9]: (k2_xboole_0(k4_xboole_0(A_841, A_9), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_841, A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44198])).
% 14.78/7.60  tff(c_44552, plain, (![A_844, A_845]: (k4_xboole_0(A_844, A_845)=k1_xboole_0 | ~r1_tarski(A_844, A_845))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_2, c_44470])).
% 14.78/7.60  tff(c_44798, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_34540, c_44552])).
% 14.78/7.60  tff(c_22, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.78/7.60  tff(c_44966, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44798, c_22])).
% 14.78/7.60  tff(c_45000, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32879, c_4, c_44966])).
% 14.78/7.60  tff(c_38380, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_subset_1(A_13, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_14, c_38206])).
% 14.78/7.60  tff(c_38560, plain, (![A_767, B_768]: (k3_subset_1(A_767, k4_xboole_0(A_767, B_768))=k3_xboole_0(A_767, B_768))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_38380])).
% 14.78/7.60  tff(c_38566, plain, (![A_767, B_768]: (k3_subset_1(A_767, k3_xboole_0(A_767, B_768))=k4_xboole_0(A_767, B_768) | ~r1_tarski(k4_xboole_0(A_767, B_768), A_767))), inference(superposition, [status(thm), theory('equality')], [c_38560, c_33549])).
% 14.78/7.60  tff(c_38596, plain, (![A_767, B_768]: (k3_subset_1(A_767, k3_xboole_0(A_767, B_768))=k4_xboole_0(A_767, B_768))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38566])).
% 14.78/7.60  tff(c_60030, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_45000, c_38596])).
% 14.78/7.60  tff(c_60116, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38841, c_60030])).
% 14.78/7.60  tff(c_60118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34453, c_60116])).
% 14.78/7.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.78/7.60  
% 14.78/7.60  Inference rules
% 14.78/7.60  ----------------------
% 14.78/7.60  #Ref     : 0
% 14.78/7.60  #Sup     : 14902
% 14.78/7.60  #Fact    : 0
% 14.78/7.60  #Define  : 0
% 14.78/7.60  #Split   : 3
% 14.78/7.60  #Chain   : 0
% 14.78/7.60  #Close   : 0
% 14.78/7.60  
% 14.78/7.60  Ordering : KBO
% 14.78/7.60  
% 14.78/7.60  Simplification rules
% 14.78/7.60  ----------------------
% 14.78/7.60  #Subsume      : 539
% 14.78/7.60  #Demod        : 12858
% 14.78/7.60  #Tautology    : 9630
% 14.78/7.60  #SimpNegUnit  : 11
% 14.78/7.60  #BackRed      : 5
% 14.78/7.60  
% 14.78/7.60  #Partial instantiations: 0
% 14.78/7.60  #Strategies tried      : 1
% 14.78/7.60  
% 14.78/7.60  Timing (in seconds)
% 14.78/7.60  ----------------------
% 14.78/7.60  Preprocessing        : 0.36
% 14.78/7.60  Parsing              : 0.19
% 14.78/7.60  CNF conversion       : 0.02
% 14.78/7.60  Main loop            : 6.44
% 14.78/7.60  Inferencing          : 1.08
% 14.78/7.61  Reduction            : 3.55
% 14.78/7.61  Demodulation         : 3.09
% 14.78/7.61  BG Simplification    : 0.12
% 14.78/7.61  Subsumption          : 1.36
% 14.78/7.61  Abstraction          : 0.19
% 14.78/7.61  MUC search           : 0.00
% 14.78/7.61  Cooper               : 0.00
% 14.78/7.61  Total                : 6.84
% 14.78/7.61  Index Insertion      : 0.00
% 14.78/7.61  Index Deletion       : 0.00
% 14.78/7.61  Index Matching       : 0.00
% 14.78/7.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
