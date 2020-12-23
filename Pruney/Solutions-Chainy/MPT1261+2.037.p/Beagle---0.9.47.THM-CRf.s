%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:16 EST 2020

% Result     : Theorem 35.27s
% Output     : CNFRefutation 35.44s
% Verified   : 
% Statistics : Number of formulae       :  261 (1171 expanded)
%              Number of leaves         :   51 ( 411 expanded)
%              Depth                    :   20
%              Number of atoms          :  357 (1800 expanded)
%              Number of equality atoms :  163 ( 747 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_108,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_89,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_91483,plain,(
    ! [A_1155,B_1156,C_1157] :
      ( k7_subset_1(A_1155,B_1156,C_1157) = k4_xboole_0(B_1156,C_1157)
      | ~ m1_subset_1(B_1156,k1_zfmisc_1(A_1155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_91492,plain,(
    ! [C_1157] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1157) = k4_xboole_0('#skF_2',C_1157) ),
    inference(resolution,[status(thm)],[c_60,c_91483])).

tff(c_93603,plain,(
    ! [A_1225,B_1226] :
      ( k7_subset_1(u1_struct_0(A_1225),B_1226,k2_tops_1(A_1225,B_1226)) = k1_tops_1(A_1225,B_1226)
      | ~ m1_subset_1(B_1226,k1_zfmisc_1(u1_struct_0(A_1225)))
      | ~ l1_pre_topc(A_1225) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_93613,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_93603])).

tff(c_93619,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91492,c_93613])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93653,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93619,c_18])).

tff(c_66,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_239,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2949,plain,(
    ! [B_236,A_237] :
      ( v4_pre_topc(B_236,A_237)
      | k2_pre_topc(A_237,B_236) != B_236
      | ~ v2_pre_topc(A_237)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2963,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2949])).

tff(c_2969,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_2963])).

tff(c_2970,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_2969])).

tff(c_138,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_138])).

tff(c_3156,plain,(
    ! [A_247,B_248] :
      ( k4_subset_1(u1_struct_0(A_247),B_248,k2_tops_1(A_247,B_248)) = k2_pre_topc(A_247,B_248)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3166,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3156])).

tff(c_3172,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3166])).

tff(c_1746,plain,(
    ! [A_185,B_186,C_187] :
      ( k7_subset_1(A_185,B_186,C_187) = k4_xboole_0(B_186,C_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1759,plain,(
    ! [C_188] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_188) = k4_xboole_0('#skF_2',C_188) ),
    inference(resolution,[status(thm)],[c_60,c_1746])).

tff(c_72,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_137,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_1765,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1759,c_137])).

tff(c_1755,plain,(
    ! [C_187] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_187) = k4_xboole_0('#skF_2',C_187) ),
    inference(resolution,[status(thm)],[c_60,c_1746])).

tff(c_3433,plain,(
    ! [A_261,B_262] :
      ( k7_subset_1(u1_struct_0(A_261),B_262,k2_tops_1(A_261,B_262)) = k1_tops_1(A_261,B_262)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3443,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3433])).

tff(c_3449,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1755,c_3443])).

tff(c_3483,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3449,c_18])).

tff(c_3493,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_3483])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1201,plain,(
    ! [A_143,B_144,C_145] :
      ( r1_tarski(A_143,k2_xboole_0(B_144,C_145))
      | ~ r1_tarski(k4_xboole_0(A_143,B_144),C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1247,plain,(
    ! [A_146,B_147] : r1_tarski(A_146,k2_xboole_0(B_147,A_146)) ),
    inference(resolution,[status(thm)],[c_8,c_1201])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1264,plain,(
    ! [A_3,B_147,A_146] :
      ( r1_tarski(A_3,k2_xboole_0(B_147,A_146))
      | ~ r1_tarski(A_3,A_146) ) ),
    inference(resolution,[status(thm)],[c_1247,c_4])).

tff(c_1532,plain,(
    ! [A_170,B_171,C_172] :
      ( r1_tarski(k4_xboole_0(A_170,B_171),C_172)
      | ~ r1_tarski(A_170,k2_xboole_0(B_171,C_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6139,plain,(
    ! [A_311,B_312,C_313] :
      ( r1_tarski(k3_xboole_0(A_311,B_312),C_313)
      | ~ r1_tarski(A_311,k2_xboole_0(k4_xboole_0(A_311,B_312),C_313)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1532])).

tff(c_6297,plain,(
    ! [A_314,B_315,A_316] :
      ( r1_tarski(k3_xboole_0(A_314,B_315),A_316)
      | ~ r1_tarski(A_314,A_316) ) ),
    inference(resolution,[status(thm)],[c_1264,c_6139])).

tff(c_13470,plain,(
    ! [A_403] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),A_403)
      | ~ r1_tarski('#skF_2',A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3493,c_6297])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2826,plain,(
    ! [A_228,B_229,C_230] :
      ( k4_subset_1(A_228,B_229,C_230) = k2_xboole_0(B_229,C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(A_228))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12180,plain,(
    ! [B_385,B_386,A_387] :
      ( k4_subset_1(B_385,B_386,A_387) = k2_xboole_0(B_386,A_387)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(B_385))
      | ~ r1_tarski(A_387,B_385) ) ),
    inference(resolution,[status(thm)],[c_44,c_2826])).

tff(c_12195,plain,(
    ! [A_387] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_387) = k2_xboole_0('#skF_2',A_387)
      | ~ r1_tarski(A_387,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_60,c_12180])).

tff(c_13474,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_13470,c_12195])).

tff(c_13562,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_3172,c_13474])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_375,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_396,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_375])).

tff(c_400,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_396])).

tff(c_411,plain,(
    ! [A_93] : r1_tarski(k1_xboole_0,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_8])).

tff(c_399,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_396])).

tff(c_1223,plain,(
    ! [A_11,C_145] :
      ( r1_tarski(A_11,k2_xboole_0(A_11,C_145))
      | ~ r1_tarski(k1_xboole_0,C_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1201])).

tff(c_1244,plain,(
    ! [A_11,C_145] : r1_tarski(A_11,k2_xboole_0(A_11,C_145)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_1223])).

tff(c_22299,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13562,c_1244])).

tff(c_22,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_163,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_183,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(B_81,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_163])).

tff(c_24,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [B_81,A_80] : k2_xboole_0(B_81,A_80) = k2_xboole_0(A_80,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_24])).

tff(c_515,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(A_100,C_101)
      | ~ r1_tarski(B_102,C_101)
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_708,plain,(
    ! [A_114,A_115,B_116] :
      ( r1_tarski(A_114,A_115)
      | ~ r1_tarski(A_114,k4_xboole_0(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_8,c_515])).

tff(c_750,plain,(
    ! [A_115,B_116,B_8] : r1_tarski(k4_xboole_0(k4_xboole_0(A_115,B_116),B_8),A_115) ),
    inference(resolution,[status(thm)],[c_8,c_708])).

tff(c_1338,plain,(
    ! [A_153,B_154,B_155] : r1_tarski(k4_xboole_0(A_153,B_154),k2_xboole_0(B_155,A_153)) ),
    inference(resolution,[status(thm)],[c_750,c_1201])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k2_xboole_0(B_16,C_17))
      | ~ r1_tarski(k4_xboole_0(A_15,B_16),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1468,plain,(
    ! [A_164,B_165,B_166] : r1_tarski(A_164,k2_xboole_0(B_165,k2_xboole_0(B_166,A_164))) ),
    inference(resolution,[status(thm)],[c_1338,c_16])).

tff(c_1494,plain,(
    ! [A_164,B_166,B_81] : r1_tarski(A_164,k2_xboole_0(k2_xboole_0(B_166,A_164),B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1468])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7923,plain,(
    ! [A_337,B_338,B_339] :
      ( k4_xboole_0(A_337,B_338) = k1_xboole_0
      | ~ r1_tarski(A_337,k2_xboole_0(B_338,k4_xboole_0(B_339,k4_xboole_0(A_337,B_338)))) ) ),
    inference(resolution,[status(thm)],[c_1532,c_10])).

tff(c_8795,plain,(
    ! [A_348,B_349] : k4_xboole_0(A_348,k2_xboole_0(B_349,A_348)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1494,c_7923])).

tff(c_8878,plain,(
    ! [A_348,B_349] : k3_xboole_0(A_348,k2_xboole_0(B_349,A_348)) = k4_xboole_0(A_348,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8795,c_18])).

tff(c_8933,plain,(
    ! [A_348,B_349] : k3_xboole_0(A_348,k2_xboole_0(B_349,A_348)) = A_348 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8878])).

tff(c_651,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4345,plain,(
    ! [B_281,A_282] :
      ( k4_xboole_0(B_281,A_282) = k3_subset_1(B_281,A_282)
      | ~ r1_tarski(A_282,B_281) ) ),
    inference(resolution,[status(thm)],[c_44,c_651])).

tff(c_4549,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = k3_subset_1(A_93,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_411,c_4345])).

tff(c_4630,plain,(
    ! [A_93] : k3_subset_1(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4549])).

tff(c_1870,plain,(
    ! [A_197,C_198] :
      ( r1_tarski(A_197,C_198)
      | ~ r1_tarski(A_197,k2_xboole_0(k1_xboole_0,C_198)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1532])).

tff(c_2228,plain,(
    ! [C_203,B_204] : r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,C_203),B_204),C_203) ),
    inference(resolution,[status(thm)],[c_8,c_1870])).

tff(c_2469,plain,(
    ! [C_213,B_214] : r1_tarski(k2_xboole_0(k1_xboole_0,C_213),k2_xboole_0(B_214,C_213)) ),
    inference(resolution,[status(thm)],[c_2228,c_16])).

tff(c_2502,plain,(
    ! [A_80,B_81] : r1_tarski(k2_xboole_0(k1_xboole_0,A_80),k2_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2469])).

tff(c_8162,plain,(
    ! [A_340] : k4_xboole_0(k2_xboole_0(k1_xboole_0,A_340),A_340) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2502,c_7923])).

tff(c_4558,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_4345])).

tff(c_4636,plain,(
    ! [A_7,B_8] : k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4558])).

tff(c_8182,plain,(
    ! [A_340] : k3_xboole_0(k2_xboole_0(k1_xboole_0,A_340),A_340) = k3_subset_1(k2_xboole_0(k1_xboole_0,A_340),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8162,c_4636])).

tff(c_26473,plain,(
    ! [A_531] : k3_xboole_0(k2_xboole_0(k1_xboole_0,A_531),A_531) = k2_xboole_0(k1_xboole_0,A_531) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_8182])).

tff(c_143,plain,(
    ! [A_72,B_73] : k1_setfam_1(k2_tarski(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_240,plain,(
    ! [A_84,B_85] : k1_setfam_1(k2_tarski(A_84,B_85)) = k3_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_40,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_246,plain,(
    ! [B_85,A_84] : k3_xboole_0(B_85,A_84) = k3_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_40])).

tff(c_26684,plain,(
    ! [A_531] : k3_xboole_0(A_531,k2_xboole_0(k1_xboole_0,A_531)) = k2_xboole_0(k1_xboole_0,A_531) ),
    inference(superposition,[status(thm),theory(equality)],[c_26473,c_246])).

tff(c_26847,plain,(
    ! [A_532] : k2_xboole_0(k1_xboole_0,A_532) = A_532 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8933,c_26684])).

tff(c_27079,plain,(
    ! [A_532] : k2_xboole_0(A_532,k1_xboole_0) = A_532 ),
    inference(superposition,[status(thm),theory(equality)],[c_26847,c_189])).

tff(c_51699,plain,(
    ! [B_748,A_749,A_750] :
      ( k4_subset_1(B_748,A_749,A_750) = k2_xboole_0(A_749,A_750)
      | ~ r1_tarski(A_750,B_748)
      | ~ r1_tarski(A_749,B_748) ) ),
    inference(resolution,[status(thm)],[c_44,c_12180])).

tff(c_51911,plain,(
    ! [A_93,A_749] :
      ( k4_subset_1(A_93,A_749,k1_xboole_0) = k2_xboole_0(A_749,k1_xboole_0)
      | ~ r1_tarski(A_749,A_93) ) ),
    inference(resolution,[status(thm)],[c_411,c_51699])).

tff(c_52028,plain,(
    ! [A_751,A_752] :
      ( k4_subset_1(A_751,A_752,k1_xboole_0) = A_752
      | ~ r1_tarski(A_752,A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27079,c_51911])).

tff(c_52395,plain,(
    k4_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',k1_xboole_0) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22299,c_52028])).

tff(c_3202,plain,(
    ! [A_251,B_252,A_253] :
      ( r1_tarski(A_251,k2_xboole_0(B_252,A_253))
      | ~ r1_tarski(A_251,A_253) ) ),
    inference(resolution,[status(thm)],[c_1247,c_4])).

tff(c_3221,plain,(
    ! [A_251,B_81,A_80] :
      ( r1_tarski(A_251,k2_xboole_0(B_81,A_80))
      | ~ r1_tarski(A_251,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_3202])).

tff(c_8057,plain,(
    ! [A_251,B_81] :
      ( k4_xboole_0(A_251,B_81) = k1_xboole_0
      | ~ r1_tarski(A_251,B_81) ) ),
    inference(resolution,[status(thm)],[c_3221,c_7923])).

tff(c_22329,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22299,c_8057])).

tff(c_22378,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22329,c_4636])).

tff(c_22433,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4630,c_22378])).

tff(c_27285,plain,(
    ! [A_534] : k2_xboole_0(A_534,k1_xboole_0) = A_534 ),
    inference(superposition,[status(thm),theory(equality)],[c_26847,c_189])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27441,plain,(
    ! [A_534] : k2_xboole_0(A_534,k1_xboole_0) = k2_xboole_0(A_534,A_534) ),
    inference(superposition,[status(thm),theory(equality)],[c_27285,c_20])).

tff(c_27505,plain,(
    ! [A_534] : k2_xboole_0(A_534,A_534) = A_534 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27079,c_27441])).

tff(c_99,plain,(
    ! [A_65,B_66] : r1_tarski(k4_xboole_0(A_65,B_66),A_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_99])).

tff(c_527,plain,(
    ! [A_100,A_7,B_8] :
      ( r1_tarski(A_100,A_7)
      | ~ r1_tarski(A_100,k4_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_8,c_515])).

tff(c_45554,plain,(
    ! [A_704,B_705,A_706,B_707] :
      ( r1_tarski(k4_xboole_0(A_704,B_705),A_706)
      | ~ r1_tarski(A_704,k2_xboole_0(B_705,k4_xboole_0(A_706,B_707))) ) ),
    inference(resolution,[status(thm)],[c_1532,c_527])).

tff(c_81065,plain,(
    ! [B_947,A_948,B_949] : r1_tarski(k4_xboole_0(k2_xboole_0(B_947,k4_xboole_0(A_948,B_949)),B_947),A_948) ),
    inference(resolution,[status(thm)],[c_102,c_45554])).

tff(c_88339,plain,(
    ! [B_1011,A_1012,B_1013] : r1_tarski(k2_xboole_0(B_1011,k4_xboole_0(A_1012,B_1013)),k2_xboole_0(B_1011,A_1012)) ),
    inference(resolution,[status(thm)],[c_81065,c_16])).

tff(c_88754,plain,(
    ! [A_1014,B_1015] : r1_tarski(k2_xboole_0(A_1014,k4_xboole_0(A_1014,B_1015)),A_1014) ),
    inference(superposition,[status(thm),theory(equality)],[c_27505,c_88339])).

tff(c_89109,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_88754])).

tff(c_89244,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13562,c_89109])).

tff(c_89270,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89244,c_8057])).

tff(c_387,plain,(
    ! [A_91,B_92] : r1_tarski(k3_xboole_0(A_91,B_92),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_8])).

tff(c_1413,plain,(
    ! [A_159,B_160] :
      ( k3_subset_1(A_159,k3_subset_1(A_159,B_160)) = B_160
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1421,plain,(
    ! [B_44,A_43] :
      ( k3_subset_1(B_44,k3_subset_1(B_44,A_43)) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_44,c_1413])).

tff(c_26,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_39,B_40] :
      ( k4_subset_1(A_39,B_40,k3_subset_1(A_39,B_40)) = k2_subset_1(A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1814,plain,(
    ! [A_192,B_193] :
      ( k4_subset_1(A_192,B_193,k3_subset_1(A_192,B_193)) = A_192
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38])).

tff(c_4979,plain,(
    ! [B_288,A_289] :
      ( k4_subset_1(B_288,A_289,k3_subset_1(B_288,A_289)) = B_288
      | ~ r1_tarski(A_289,B_288) ) ),
    inference(resolution,[status(thm)],[c_44,c_1814])).

tff(c_66322,plain,(
    ! [B_846,A_847] :
      ( k4_subset_1(B_846,k3_subset_1(B_846,A_847),A_847) = B_846
      | ~ r1_tarski(k3_subset_1(B_846,A_847),B_846)
      | ~ r1_tarski(A_847,B_846) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_4979])).

tff(c_66346,plain,(
    ! [A_7,B_8] :
      ( k4_subset_1(A_7,k3_subset_1(A_7,k4_xboole_0(A_7,B_8)),k4_xboole_0(A_7,B_8)) = A_7
      | ~ r1_tarski(k3_xboole_0(A_7,B_8),A_7)
      | ~ r1_tarski(k4_xboole_0(A_7,B_8),A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4636,c_66322])).

tff(c_76606,plain,(
    ! [A_916,B_917] : k4_subset_1(A_916,k3_xboole_0(A_916,B_917),k4_xboole_0(A_916,B_917)) = A_916 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_387,c_4636,c_66346])).

tff(c_76975,plain,(
    ! [B_85,A_84] : k4_subset_1(B_85,k3_xboole_0(A_84,B_85),k4_xboole_0(B_85,A_84)) = B_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_76606])).

tff(c_89287,plain,(
    k4_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')),k1_xboole_0) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89270,c_76975])).

tff(c_89466,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52395,c_22433,c_89287])).

tff(c_89468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2970,c_89466])).

tff(c_89469,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_89633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89469,c_137])).

tff(c_89634,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_89752,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89634,c_66])).

tff(c_91764,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91492,c_89752])).

tff(c_130650,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93653,c_91764])).

tff(c_92468,plain,(
    ! [A_1189,B_1190] :
      ( k2_pre_topc(A_1189,B_1190) = B_1190
      | ~ v4_pre_topc(B_1190,A_1189)
      | ~ m1_subset_1(B_1190,k1_zfmisc_1(u1_struct_0(A_1189)))
      | ~ l1_pre_topc(A_1189) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_92482,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_92468])).

tff(c_92488,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_89634,c_92482])).

tff(c_93817,plain,(
    ! [A_1232,B_1233] :
      ( k4_subset_1(u1_struct_0(A_1232),B_1233,k2_tops_1(A_1232,B_1233)) = k2_pre_topc(A_1232,B_1233)
      | ~ m1_subset_1(B_1233,k1_zfmisc_1(u1_struct_0(A_1232)))
      | ~ l1_pre_topc(A_1232) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_93827,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_93817])).

tff(c_93833,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_92488,c_93827])).

tff(c_50,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k2_tops_1(A_48,B_49),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_92575,plain,(
    ! [A_1194,B_1195,C_1196] :
      ( k4_subset_1(A_1194,B_1195,C_1196) = k2_xboole_0(B_1195,C_1196)
      | ~ m1_subset_1(C_1196,k1_zfmisc_1(A_1194))
      | ~ m1_subset_1(B_1195,k1_zfmisc_1(A_1194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_123648,plain,(
    ! [A_1597,B_1598,B_1599] :
      ( k4_subset_1(u1_struct_0(A_1597),B_1598,k2_tops_1(A_1597,B_1599)) = k2_xboole_0(B_1598,k2_tops_1(A_1597,B_1599))
      | ~ m1_subset_1(B_1598,k1_zfmisc_1(u1_struct_0(A_1597)))
      | ~ m1_subset_1(B_1599,k1_zfmisc_1(u1_struct_0(A_1597)))
      | ~ l1_pre_topc(A_1597) ) ),
    inference(resolution,[status(thm)],[c_50,c_92575])).

tff(c_123664,plain,(
    ! [B_1599] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_1599)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_1599))
      | ~ m1_subset_1(B_1599,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_60,c_123648])).

tff(c_155927,plain,(
    ! [B_1856] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_1856)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_1856))
      | ~ m1_subset_1(B_1856,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_123664])).

tff(c_155950,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_155927])).

tff(c_155959,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93833,c_155950])).

tff(c_89789,plain,(
    ! [A_1041,B_1042] : k4_xboole_0(A_1041,k4_xboole_0(A_1041,B_1042)) = k3_xboole_0(A_1041,B_1042) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89810,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89789])).

tff(c_89814,plain,(
    ! [A_1043] : k4_xboole_0(A_1043,A_1043) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_89810])).

tff(c_89819,plain,(
    ! [A_1043] : k4_xboole_0(A_1043,k1_xboole_0) = k3_xboole_0(A_1043,A_1043) ),
    inference(superposition,[status(thm),theory(equality)],[c_89814,c_18])).

tff(c_89837,plain,(
    ! [A_1043] : k3_xboole_0(A_1043,A_1043) = A_1043 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89819])).

tff(c_89661,plain,(
    ! [A_1032,B_1033] : k3_tarski(k2_tarski(A_1032,B_1033)) = k2_xboole_0(A_1032,B_1033) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90065,plain,(
    ! [B_1058,A_1059] : k3_tarski(k2_tarski(B_1058,A_1059)) = k2_xboole_0(A_1059,B_1058) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_89661])).

tff(c_90071,plain,(
    ! [B_1058,A_1059] : k2_xboole_0(B_1058,A_1059) = k2_xboole_0(A_1059,B_1058) ),
    inference(superposition,[status(thm),theory(equality)],[c_90065,c_24])).

tff(c_90129,plain,(
    ! [A_1062,C_1063,B_1064] :
      ( r1_tarski(A_1062,C_1063)
      | ~ r1_tarski(B_1064,C_1063)
      | ~ r1_tarski(A_1062,B_1064) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90178,plain,(
    ! [A_1068,A_1069,B_1070] :
      ( r1_tarski(A_1068,A_1069)
      | ~ r1_tarski(A_1068,k4_xboole_0(A_1069,B_1070)) ) ),
    inference(resolution,[status(thm)],[c_8,c_90129])).

tff(c_90217,plain,(
    ! [A_1069,B_1070,B_8] : r1_tarski(k4_xboole_0(k4_xboole_0(A_1069,B_1070),B_8),A_1069) ),
    inference(resolution,[status(thm)],[c_8,c_90178])).

tff(c_90461,plain,(
    ! [A_1085,B_1086,C_1087] :
      ( r1_tarski(A_1085,k2_xboole_0(B_1086,C_1087))
      | ~ r1_tarski(k4_xboole_0(A_1085,B_1086),C_1087) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90596,plain,(
    ! [A_1096,B_1097,B_1098] : r1_tarski(k4_xboole_0(A_1096,B_1097),k2_xboole_0(B_1098,A_1096)) ),
    inference(resolution,[status(thm)],[c_90217,c_90461])).

tff(c_90699,plain,(
    ! [A_1104,B_1105,B_1106] : r1_tarski(A_1104,k2_xboole_0(B_1105,k2_xboole_0(B_1106,A_1104))) ),
    inference(resolution,[status(thm)],[c_90596,c_16])).

tff(c_90721,plain,(
    ! [A_1104,B_1106,B_1058] : r1_tarski(A_1104,k2_xboole_0(k2_xboole_0(B_1106,A_1104),B_1058)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90071,c_90699])).

tff(c_91280,plain,(
    ! [A_1141,B_1142,C_1143] :
      ( r1_tarski(k4_xboole_0(A_1141,B_1142),C_1143)
      | ~ r1_tarski(A_1141,k2_xboole_0(B_1142,C_1143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100561,plain,(
    ! [A_1390,B_1391,B_1392] :
      ( k4_xboole_0(A_1390,B_1391) = k1_xboole_0
      | ~ r1_tarski(A_1390,k2_xboole_0(B_1391,k4_xboole_0(B_1392,k4_xboole_0(A_1390,B_1391)))) ) ),
    inference(resolution,[status(thm)],[c_91280,c_10])).

tff(c_101849,plain,(
    ! [A_1403,B_1404] : k4_xboole_0(A_1403,k2_xboole_0(B_1404,A_1403)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90721,c_100561])).

tff(c_102022,plain,(
    ! [A_1403,B_1404] : k3_xboole_0(A_1403,k2_xboole_0(B_1404,A_1403)) = k4_xboole_0(A_1403,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_101849,c_18])).

tff(c_102107,plain,(
    ! [A_1403,B_1404] : k3_xboole_0(A_1403,k2_xboole_0(B_1404,A_1403)) = A_1403 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_102022])).

tff(c_89641,plain,(
    ! [A_1028,B_1029] : k1_setfam_1(k2_tarski(A_1028,B_1029)) = k3_xboole_0(A_1028,B_1029) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89681,plain,(
    ! [A_1036,B_1037] : k1_setfam_1(k2_tarski(A_1036,B_1037)) = k3_xboole_0(B_1037,A_1036) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_89641])).

tff(c_89687,plain,(
    ! [B_1037,A_1036] : k3_xboole_0(B_1037,A_1036) = k3_xboole_0(A_1036,B_1037) ),
    inference(superposition,[status(thm),theory(equality)],[c_89681,c_40])).

tff(c_89825,plain,(
    ! [A_1043] : r1_tarski(k1_xboole_0,A_1043) ),
    inference(superposition,[status(thm),theory(equality)],[c_89814,c_8])).

tff(c_90690,plain,(
    ! [A_1102,B_1103] :
      ( k4_xboole_0(A_1102,B_1103) = k3_subset_1(A_1102,B_1103)
      | ~ m1_subset_1(B_1103,k1_zfmisc_1(A_1102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94172,plain,(
    ! [B_1242,A_1243] :
      ( k4_xboole_0(B_1242,A_1243) = k3_subset_1(B_1242,A_1243)
      | ~ r1_tarski(A_1243,B_1242) ) ),
    inference(resolution,[status(thm)],[c_44,c_90690])).

tff(c_94370,plain,(
    ! [A_1043] : k4_xboole_0(A_1043,k1_xboole_0) = k3_subset_1(A_1043,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_89825,c_94172])).

tff(c_94447,plain,(
    ! [A_1043] : k3_subset_1(A_1043,k1_xboole_0) = A_1043 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_94370])).

tff(c_91493,plain,(
    ! [A_1158,C_1159] :
      ( r1_tarski(A_1158,C_1159)
      | ~ r1_tarski(A_1158,k2_xboole_0(k1_xboole_0,C_1159)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_91280])).

tff(c_91820,plain,(
    ! [C_1163,B_1164] : r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,C_1163),B_1164),C_1163) ),
    inference(resolution,[status(thm)],[c_8,c_91493])).

tff(c_92138,plain,(
    ! [C_1175,B_1176] : r1_tarski(k2_xboole_0(k1_xboole_0,C_1175),k2_xboole_0(B_1176,C_1175)) ),
    inference(resolution,[status(thm)],[c_91820,c_16])).

tff(c_92166,plain,(
    ! [A_1059,B_1058] : r1_tarski(k2_xboole_0(k1_xboole_0,A_1059),k2_xboole_0(A_1059,B_1058)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90071,c_92138])).

tff(c_100744,plain,(
    ! [A_1393] : k4_xboole_0(k2_xboole_0(k1_xboole_0,A_1393),A_1393) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92166,c_100561])).

tff(c_94379,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_94172])).

tff(c_94453,plain,(
    ! [A_7,B_8] : k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_94379])).

tff(c_100797,plain,(
    ! [A_1393] : k3_xboole_0(k2_xboole_0(k1_xboole_0,A_1393),A_1393) = k3_subset_1(k2_xboole_0(k1_xboole_0,A_1393),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100744,c_94453])).

tff(c_116611,plain,(
    ! [A_1524] : k3_xboole_0(k2_xboole_0(k1_xboole_0,A_1524),A_1524) = k2_xboole_0(k1_xboole_0,A_1524) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94447,c_100797])).

tff(c_116839,plain,(
    ! [A_1524] : k3_xboole_0(A_1524,k2_xboole_0(k1_xboole_0,A_1524)) = k2_xboole_0(k1_xboole_0,A_1524) ),
    inference(superposition,[status(thm),theory(equality)],[c_116611,c_89687])).

tff(c_117012,plain,(
    ! [A_1525] : k2_xboole_0(k1_xboole_0,A_1525) = A_1525 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102107,c_116839])).

tff(c_117302,plain,(
    ! [A_1059] : k2_xboole_0(A_1059,k1_xboole_0) = A_1059 ),
    inference(superposition,[status(thm),theory(equality)],[c_90071,c_117012])).

tff(c_90606,plain,(
    ! [B_1058,B_1097,A_1059] : r1_tarski(k4_xboole_0(B_1058,B_1097),k2_xboole_0(B_1058,A_1059)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90071,c_90596])).

tff(c_100912,plain,(
    ! [B_1394,B_1395] : k4_xboole_0(k4_xboole_0(B_1394,B_1395),B_1394) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90606,c_100561])).

tff(c_101321,plain,(
    ! [A_1396,B_1397] : k4_xboole_0(k3_xboole_0(A_1396,B_1397),A_1396) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_100912])).

tff(c_101431,plain,(
    ! [A_1036,B_1037] : k4_xboole_0(k3_xboole_0(A_1036,B_1037),B_1037) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89687,c_101321])).

tff(c_90498,plain,(
    ! [A_1085,B_1086] : r1_tarski(A_1085,k2_xboole_0(B_1086,k4_xboole_0(A_1085,B_1086))) ),
    inference(resolution,[status(thm)],[c_102,c_90461])).

tff(c_90500,plain,(
    ! [A_1088,B_1089] : r1_tarski(A_1088,k2_xboole_0(B_1089,A_1088)) ),
    inference(resolution,[status(thm)],[c_8,c_90461])).

tff(c_92814,plain,(
    ! [A_1203,B_1204,A_1205] :
      ( r1_tarski(A_1203,k2_xboole_0(B_1204,A_1205))
      | ~ r1_tarski(A_1203,A_1205) ) ),
    inference(resolution,[status(thm)],[c_90500,c_4])).

tff(c_92835,plain,(
    ! [A_1203,A_1059,B_1058] :
      ( r1_tarski(A_1203,k2_xboole_0(A_1059,B_1058))
      | ~ r1_tarski(A_1203,A_1059) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90071,c_92814])).

tff(c_103298,plain,(
    ! [A_1417,A_1418] :
      ( k4_xboole_0(A_1417,A_1418) = k1_xboole_0
      | ~ r1_tarski(A_1417,A_1418) ) ),
    inference(resolution,[status(thm)],[c_92835,c_100561])).

tff(c_113350,plain,(
    ! [A_1501,B_1502] : k4_xboole_0(A_1501,k2_xboole_0(B_1502,k4_xboole_0(A_1501,B_1502))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90498,c_103298])).

tff(c_113505,plain,(
    ! [A_1501,B_1502] : k3_xboole_0(A_1501,k2_xboole_0(B_1502,k4_xboole_0(A_1501,B_1502))) = k3_subset_1(A_1501,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113350,c_94453])).

tff(c_118378,plain,(
    ! [A_1540,B_1541] : k3_xboole_0(A_1540,k2_xboole_0(B_1541,k4_xboole_0(A_1540,B_1541))) = A_1540 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94447,c_113505])).

tff(c_118698,plain,(
    ! [A_1036,B_1037] : k3_xboole_0(k3_xboole_0(A_1036,B_1037),k2_xboole_0(B_1037,k1_xboole_0)) = k3_xboole_0(A_1036,B_1037) ),
    inference(superposition,[status(thm),theory(equality)],[c_101431,c_118378])).

tff(c_133445,plain,(
    ! [B_1684,A_1685] : k3_xboole_0(B_1684,k3_xboole_0(A_1685,B_1684)) = k3_xboole_0(A_1685,B_1684) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89687,c_117302,c_118698])).

tff(c_134092,plain,(
    ! [A_1687,B_1688] : k3_xboole_0(A_1687,k3_xboole_0(A_1687,B_1688)) = k3_xboole_0(B_1688,A_1687) ),
    inference(superposition,[status(thm),theory(equality)],[c_89687,c_133445])).

tff(c_134481,plain,(
    ! [B_1404,A_1403] : k3_xboole_0(k2_xboole_0(B_1404,A_1403),A_1403) = k3_xboole_0(A_1403,A_1403) ),
    inference(superposition,[status(thm),theory(equality)],[c_102107,c_134092])).

tff(c_134598,plain,(
    ! [B_1404,A_1403] : k3_xboole_0(k2_xboole_0(B_1404,A_1403),A_1403) = A_1403 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89837,c_134481])).

tff(c_156028,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_155959,c_134598])).

tff(c_156185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130650,c_156028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.27/25.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.44/25.66  
% 35.44/25.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.44/25.67  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 35.44/25.67  
% 35.44/25.67  %Foreground sorts:
% 35.44/25.67  
% 35.44/25.67  
% 35.44/25.67  %Background operators:
% 35.44/25.67  
% 35.44/25.67  
% 35.44/25.67  %Foreground operators:
% 35.44/25.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.44/25.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 35.44/25.67  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 35.44/25.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 35.44/25.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 35.44/25.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 35.44/25.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 35.44/25.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 35.44/25.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 35.44/25.67  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 35.44/25.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 35.44/25.67  tff('#skF_2', type, '#skF_2': $i).
% 35.44/25.67  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 35.44/25.67  tff('#skF_1', type, '#skF_1': $i).
% 35.44/25.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 35.44/25.67  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 35.44/25.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.44/25.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 35.44/25.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.44/25.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 35.44/25.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 35.44/25.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 35.44/25.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 35.44/25.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 35.44/25.67  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 35.44/25.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 35.44/25.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 35.44/25.67  
% 35.44/25.70  tff(f_155, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 35.44/25.70  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 35.44/25.70  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 35.44/25.70  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 35.44/25.70  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 35.44/25.70  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 35.44/25.70  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 35.44/25.70  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 35.44/25.70  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 35.44/25.70  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 35.44/25.70  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 35.44/25.70  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 35.44/25.70  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 35.44/25.70  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 35.44/25.70  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 35.44/25.70  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 35.44/25.70  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 35.44/25.70  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 35.44/25.70  tff(f_89, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 35.44/25.70  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 35.44/25.70  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 35.44/25.70  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 35.44/25.70  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 35.44/25.70  tff(f_114, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 35.44/25.70  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.44/25.70  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.44/25.70  tff(c_91483, plain, (![A_1155, B_1156, C_1157]: (k7_subset_1(A_1155, B_1156, C_1157)=k4_xboole_0(B_1156, C_1157) | ~m1_subset_1(B_1156, k1_zfmisc_1(A_1155)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 35.44/25.70  tff(c_91492, plain, (![C_1157]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1157)=k4_xboole_0('#skF_2', C_1157))), inference(resolution, [status(thm)], [c_60, c_91483])).
% 35.44/25.70  tff(c_93603, plain, (![A_1225, B_1226]: (k7_subset_1(u1_struct_0(A_1225), B_1226, k2_tops_1(A_1225, B_1226))=k1_tops_1(A_1225, B_1226) | ~m1_subset_1(B_1226, k1_zfmisc_1(u1_struct_0(A_1225))) | ~l1_pre_topc(A_1225))), inference(cnfTransformation, [status(thm)], [f_143])).
% 35.44/25.70  tff(c_93613, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_93603])).
% 35.44/25.70  tff(c_93619, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91492, c_93613])).
% 35.44/25.70  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 35.44/25.70  tff(c_93653, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_93619, c_18])).
% 35.44/25.70  tff(c_66, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.44/25.70  tff(c_239, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 35.44/25.70  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.44/25.70  tff(c_2949, plain, (![B_236, A_237]: (v4_pre_topc(B_236, A_237) | k2_pre_topc(A_237, B_236)!=B_236 | ~v2_pre_topc(A_237) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_108])).
% 35.44/25.70  tff(c_2963, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2949])).
% 35.44/25.70  tff(c_2969, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_2963])).
% 35.44/25.70  tff(c_2970, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_239, c_2969])).
% 35.44/25.70  tff(c_138, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 35.44/25.70  tff(c_142, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_138])).
% 35.44/25.70  tff(c_3156, plain, (![A_247, B_248]: (k4_subset_1(u1_struct_0(A_247), B_248, k2_tops_1(A_247, B_248))=k2_pre_topc(A_247, B_248) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_136])).
% 35.44/25.70  tff(c_3166, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3156])).
% 35.44/25.70  tff(c_3172, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3166])).
% 35.44/25.70  tff(c_1746, plain, (![A_185, B_186, C_187]: (k7_subset_1(A_185, B_186, C_187)=k4_xboole_0(B_186, C_187) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 35.44/25.70  tff(c_1759, plain, (![C_188]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_188)=k4_xboole_0('#skF_2', C_188))), inference(resolution, [status(thm)], [c_60, c_1746])).
% 35.44/25.70  tff(c_72, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.44/25.70  tff(c_137, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_72])).
% 35.44/25.70  tff(c_1765, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1759, c_137])).
% 35.44/25.70  tff(c_1755, plain, (![C_187]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_187)=k4_xboole_0('#skF_2', C_187))), inference(resolution, [status(thm)], [c_60, c_1746])).
% 35.44/25.70  tff(c_3433, plain, (![A_261, B_262]: (k7_subset_1(u1_struct_0(A_261), B_262, k2_tops_1(A_261, B_262))=k1_tops_1(A_261, B_262) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_143])).
% 35.44/25.70  tff(c_3443, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3433])).
% 35.44/25.70  tff(c_3449, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1755, c_3443])).
% 35.44/25.70  tff(c_3483, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3449, c_18])).
% 35.44/25.70  tff(c_3493, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_3483])).
% 35.44/25.70  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.44/25.70  tff(c_1201, plain, (![A_143, B_144, C_145]: (r1_tarski(A_143, k2_xboole_0(B_144, C_145)) | ~r1_tarski(k4_xboole_0(A_143, B_144), C_145))), inference(cnfTransformation, [status(thm)], [f_51])).
% 35.44/25.70  tff(c_1247, plain, (![A_146, B_147]: (r1_tarski(A_146, k2_xboole_0(B_147, A_146)))), inference(resolution, [status(thm)], [c_8, c_1201])).
% 35.44/25.70  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 35.44/25.70  tff(c_1264, plain, (![A_3, B_147, A_146]: (r1_tarski(A_3, k2_xboole_0(B_147, A_146)) | ~r1_tarski(A_3, A_146))), inference(resolution, [status(thm)], [c_1247, c_4])).
% 35.44/25.70  tff(c_1532, plain, (![A_170, B_171, C_172]: (r1_tarski(k4_xboole_0(A_170, B_171), C_172) | ~r1_tarski(A_170, k2_xboole_0(B_171, C_172)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 35.44/25.70  tff(c_6139, plain, (![A_311, B_312, C_313]: (r1_tarski(k3_xboole_0(A_311, B_312), C_313) | ~r1_tarski(A_311, k2_xboole_0(k4_xboole_0(A_311, B_312), C_313)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1532])).
% 35.44/25.70  tff(c_6297, plain, (![A_314, B_315, A_316]: (r1_tarski(k3_xboole_0(A_314, B_315), A_316) | ~r1_tarski(A_314, A_316))), inference(resolution, [status(thm)], [c_1264, c_6139])).
% 35.44/25.70  tff(c_13470, plain, (![A_403]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), A_403) | ~r1_tarski('#skF_2', A_403))), inference(superposition, [status(thm), theory('equality')], [c_3493, c_6297])).
% 35.44/25.70  tff(c_44, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 35.44/25.70  tff(c_2826, plain, (![A_228, B_229, C_230]: (k4_subset_1(A_228, B_229, C_230)=k2_xboole_0(B_229, C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(A_228)) | ~m1_subset_1(B_229, k1_zfmisc_1(A_228)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 35.44/25.70  tff(c_12180, plain, (![B_385, B_386, A_387]: (k4_subset_1(B_385, B_386, A_387)=k2_xboole_0(B_386, A_387) | ~m1_subset_1(B_386, k1_zfmisc_1(B_385)) | ~r1_tarski(A_387, B_385))), inference(resolution, [status(thm)], [c_44, c_2826])).
% 35.44/25.70  tff(c_12195, plain, (![A_387]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_387)=k2_xboole_0('#skF_2', A_387) | ~r1_tarski(A_387, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_12180])).
% 35.44/25.70  tff(c_13474, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_13470, c_12195])).
% 35.44/25.70  tff(c_13562, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_3172, c_13474])).
% 35.44/25.70  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 35.44/25.70  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 35.44/25.70  tff(c_375, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 35.44/25.70  tff(c_396, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_375])).
% 35.44/25.70  tff(c_400, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_396])).
% 35.44/25.70  tff(c_411, plain, (![A_93]: (r1_tarski(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_400, c_8])).
% 35.44/25.70  tff(c_399, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_396])).
% 35.44/25.70  tff(c_1223, plain, (![A_11, C_145]: (r1_tarski(A_11, k2_xboole_0(A_11, C_145)) | ~r1_tarski(k1_xboole_0, C_145))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1201])).
% 35.44/25.70  tff(c_1244, plain, (![A_11, C_145]: (r1_tarski(A_11, k2_xboole_0(A_11, C_145)))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_1223])).
% 35.44/25.70  tff(c_22299, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13562, c_1244])).
% 35.44/25.70  tff(c_22, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 35.44/25.70  tff(c_163, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 35.44/25.70  tff(c_183, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(B_81, A_80))), inference(superposition, [status(thm), theory('equality')], [c_22, c_163])).
% 35.44/25.70  tff(c_24, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 35.44/25.70  tff(c_189, plain, (![B_81, A_80]: (k2_xboole_0(B_81, A_80)=k2_xboole_0(A_80, B_81))), inference(superposition, [status(thm), theory('equality')], [c_183, c_24])).
% 35.44/25.70  tff(c_515, plain, (![A_100, C_101, B_102]: (r1_tarski(A_100, C_101) | ~r1_tarski(B_102, C_101) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_33])).
% 35.44/25.70  tff(c_708, plain, (![A_114, A_115, B_116]: (r1_tarski(A_114, A_115) | ~r1_tarski(A_114, k4_xboole_0(A_115, B_116)))), inference(resolution, [status(thm)], [c_8, c_515])).
% 35.44/25.70  tff(c_750, plain, (![A_115, B_116, B_8]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_115, B_116), B_8), A_115))), inference(resolution, [status(thm)], [c_8, c_708])).
% 35.44/25.70  tff(c_1338, plain, (![A_153, B_154, B_155]: (r1_tarski(k4_xboole_0(A_153, B_154), k2_xboole_0(B_155, A_153)))), inference(resolution, [status(thm)], [c_750, c_1201])).
% 35.44/25.70  tff(c_16, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k2_xboole_0(B_16, C_17)) | ~r1_tarski(k4_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 35.44/25.70  tff(c_1468, plain, (![A_164, B_165, B_166]: (r1_tarski(A_164, k2_xboole_0(B_165, k2_xboole_0(B_166, A_164))))), inference(resolution, [status(thm)], [c_1338, c_16])).
% 35.44/25.70  tff(c_1494, plain, (![A_164, B_166, B_81]: (r1_tarski(A_164, k2_xboole_0(k2_xboole_0(B_166, A_164), B_81)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_1468])).
% 35.44/25.70  tff(c_10, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 35.44/25.70  tff(c_7923, plain, (![A_337, B_338, B_339]: (k4_xboole_0(A_337, B_338)=k1_xboole_0 | ~r1_tarski(A_337, k2_xboole_0(B_338, k4_xboole_0(B_339, k4_xboole_0(A_337, B_338)))))), inference(resolution, [status(thm)], [c_1532, c_10])).
% 35.44/25.70  tff(c_8795, plain, (![A_348, B_349]: (k4_xboole_0(A_348, k2_xboole_0(B_349, A_348))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1494, c_7923])).
% 35.44/25.70  tff(c_8878, plain, (![A_348, B_349]: (k3_xboole_0(A_348, k2_xboole_0(B_349, A_348))=k4_xboole_0(A_348, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8795, c_18])).
% 35.44/25.70  tff(c_8933, plain, (![A_348, B_349]: (k3_xboole_0(A_348, k2_xboole_0(B_349, A_348))=A_348)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8878])).
% 35.44/25.70  tff(c_651, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 35.44/25.70  tff(c_4345, plain, (![B_281, A_282]: (k4_xboole_0(B_281, A_282)=k3_subset_1(B_281, A_282) | ~r1_tarski(A_282, B_281))), inference(resolution, [status(thm)], [c_44, c_651])).
% 35.44/25.70  tff(c_4549, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=k3_subset_1(A_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_411, c_4345])).
% 35.44/25.70  tff(c_4630, plain, (![A_93]: (k3_subset_1(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4549])).
% 35.44/25.70  tff(c_1870, plain, (![A_197, C_198]: (r1_tarski(A_197, C_198) | ~r1_tarski(A_197, k2_xboole_0(k1_xboole_0, C_198)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1532])).
% 35.44/25.70  tff(c_2228, plain, (![C_203, B_204]: (r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0, C_203), B_204), C_203))), inference(resolution, [status(thm)], [c_8, c_1870])).
% 35.44/25.70  tff(c_2469, plain, (![C_213, B_214]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_213), k2_xboole_0(B_214, C_213)))), inference(resolution, [status(thm)], [c_2228, c_16])).
% 35.44/25.70  tff(c_2502, plain, (![A_80, B_81]: (r1_tarski(k2_xboole_0(k1_xboole_0, A_80), k2_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_2469])).
% 35.44/25.70  tff(c_8162, plain, (![A_340]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, A_340), A_340)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2502, c_7923])).
% 35.44/25.70  tff(c_4558, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_4345])).
% 35.44/25.70  tff(c_4636, plain, (![A_7, B_8]: (k3_subset_1(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4558])).
% 35.44/25.70  tff(c_8182, plain, (![A_340]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, A_340), A_340)=k3_subset_1(k2_xboole_0(k1_xboole_0, A_340), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8162, c_4636])).
% 35.44/25.70  tff(c_26473, plain, (![A_531]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, A_531), A_531)=k2_xboole_0(k1_xboole_0, A_531))), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_8182])).
% 35.44/25.70  tff(c_143, plain, (![A_72, B_73]: (k1_setfam_1(k2_tarski(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_89])).
% 35.44/25.70  tff(c_240, plain, (![A_84, B_85]: (k1_setfam_1(k2_tarski(A_84, B_85))=k3_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_22, c_143])).
% 35.44/25.70  tff(c_40, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 35.44/25.70  tff(c_246, plain, (![B_85, A_84]: (k3_xboole_0(B_85, A_84)=k3_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_240, c_40])).
% 35.44/25.70  tff(c_26684, plain, (![A_531]: (k3_xboole_0(A_531, k2_xboole_0(k1_xboole_0, A_531))=k2_xboole_0(k1_xboole_0, A_531))), inference(superposition, [status(thm), theory('equality')], [c_26473, c_246])).
% 35.44/25.70  tff(c_26847, plain, (![A_532]: (k2_xboole_0(k1_xboole_0, A_532)=A_532)), inference(demodulation, [status(thm), theory('equality')], [c_8933, c_26684])).
% 35.44/25.70  tff(c_27079, plain, (![A_532]: (k2_xboole_0(A_532, k1_xboole_0)=A_532)), inference(superposition, [status(thm), theory('equality')], [c_26847, c_189])).
% 35.44/25.70  tff(c_51699, plain, (![B_748, A_749, A_750]: (k4_subset_1(B_748, A_749, A_750)=k2_xboole_0(A_749, A_750) | ~r1_tarski(A_750, B_748) | ~r1_tarski(A_749, B_748))), inference(resolution, [status(thm)], [c_44, c_12180])).
% 35.44/25.70  tff(c_51911, plain, (![A_93, A_749]: (k4_subset_1(A_93, A_749, k1_xboole_0)=k2_xboole_0(A_749, k1_xboole_0) | ~r1_tarski(A_749, A_93))), inference(resolution, [status(thm)], [c_411, c_51699])).
% 35.44/25.70  tff(c_52028, plain, (![A_751, A_752]: (k4_subset_1(A_751, A_752, k1_xboole_0)=A_752 | ~r1_tarski(A_752, A_751))), inference(demodulation, [status(thm), theory('equality')], [c_27079, c_51911])).
% 35.44/25.70  tff(c_52395, plain, (k4_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', k1_xboole_0)='#skF_2'), inference(resolution, [status(thm)], [c_22299, c_52028])).
% 35.44/25.70  tff(c_3202, plain, (![A_251, B_252, A_253]: (r1_tarski(A_251, k2_xboole_0(B_252, A_253)) | ~r1_tarski(A_251, A_253))), inference(resolution, [status(thm)], [c_1247, c_4])).
% 35.44/25.70  tff(c_3221, plain, (![A_251, B_81, A_80]: (r1_tarski(A_251, k2_xboole_0(B_81, A_80)) | ~r1_tarski(A_251, B_81))), inference(superposition, [status(thm), theory('equality')], [c_189, c_3202])).
% 35.44/25.70  tff(c_8057, plain, (![A_251, B_81]: (k4_xboole_0(A_251, B_81)=k1_xboole_0 | ~r1_tarski(A_251, B_81))), inference(resolution, [status(thm)], [c_3221, c_7923])).
% 35.44/25.70  tff(c_22329, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22299, c_8057])).
% 35.44/25.70  tff(c_22378, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22329, c_4636])).
% 35.44/25.70  tff(c_22433, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4630, c_22378])).
% 35.44/25.70  tff(c_27285, plain, (![A_534]: (k2_xboole_0(A_534, k1_xboole_0)=A_534)), inference(superposition, [status(thm), theory('equality')], [c_26847, c_189])).
% 35.44/25.70  tff(c_20, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 35.44/25.70  tff(c_27441, plain, (![A_534]: (k2_xboole_0(A_534, k1_xboole_0)=k2_xboole_0(A_534, A_534))), inference(superposition, [status(thm), theory('equality')], [c_27285, c_20])).
% 35.44/25.70  tff(c_27505, plain, (![A_534]: (k2_xboole_0(A_534, A_534)=A_534)), inference(demodulation, [status(thm), theory('equality')], [c_27079, c_27441])).
% 35.44/25.70  tff(c_99, plain, (![A_65, B_66]: (r1_tarski(k4_xboole_0(A_65, B_66), A_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.44/25.70  tff(c_102, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_99])).
% 35.44/25.70  tff(c_527, plain, (![A_100, A_7, B_8]: (r1_tarski(A_100, A_7) | ~r1_tarski(A_100, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_515])).
% 35.44/25.70  tff(c_45554, plain, (![A_704, B_705, A_706, B_707]: (r1_tarski(k4_xboole_0(A_704, B_705), A_706) | ~r1_tarski(A_704, k2_xboole_0(B_705, k4_xboole_0(A_706, B_707))))), inference(resolution, [status(thm)], [c_1532, c_527])).
% 35.44/25.70  tff(c_81065, plain, (![B_947, A_948, B_949]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_947, k4_xboole_0(A_948, B_949)), B_947), A_948))), inference(resolution, [status(thm)], [c_102, c_45554])).
% 35.44/25.70  tff(c_88339, plain, (![B_1011, A_1012, B_1013]: (r1_tarski(k2_xboole_0(B_1011, k4_xboole_0(A_1012, B_1013)), k2_xboole_0(B_1011, A_1012)))), inference(resolution, [status(thm)], [c_81065, c_16])).
% 35.44/25.70  tff(c_88754, plain, (![A_1014, B_1015]: (r1_tarski(k2_xboole_0(A_1014, k4_xboole_0(A_1014, B_1015)), A_1014))), inference(superposition, [status(thm), theory('equality')], [c_27505, c_88339])).
% 35.44/25.70  tff(c_89109, plain, (r1_tarski(k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1765, c_88754])).
% 35.44/25.70  tff(c_89244, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13562, c_89109])).
% 35.44/25.70  tff(c_89270, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_89244, c_8057])).
% 35.44/25.70  tff(c_387, plain, (![A_91, B_92]: (r1_tarski(k3_xboole_0(A_91, B_92), A_91))), inference(superposition, [status(thm), theory('equality')], [c_375, c_8])).
% 35.44/25.70  tff(c_1413, plain, (![A_159, B_160]: (k3_subset_1(A_159, k3_subset_1(A_159, B_160))=B_160 | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 35.44/25.70  tff(c_1421, plain, (![B_44, A_43]: (k3_subset_1(B_44, k3_subset_1(B_44, A_43))=A_43 | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_44, c_1413])).
% 35.44/25.70  tff(c_26, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_61])).
% 35.44/25.70  tff(c_38, plain, (![A_39, B_40]: (k4_subset_1(A_39, B_40, k3_subset_1(A_39, B_40))=k2_subset_1(A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 35.44/25.70  tff(c_1814, plain, (![A_192, B_193]: (k4_subset_1(A_192, B_193, k3_subset_1(A_192, B_193))=A_192 | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38])).
% 35.44/25.70  tff(c_4979, plain, (![B_288, A_289]: (k4_subset_1(B_288, A_289, k3_subset_1(B_288, A_289))=B_288 | ~r1_tarski(A_289, B_288))), inference(resolution, [status(thm)], [c_44, c_1814])).
% 35.44/25.70  tff(c_66322, plain, (![B_846, A_847]: (k4_subset_1(B_846, k3_subset_1(B_846, A_847), A_847)=B_846 | ~r1_tarski(k3_subset_1(B_846, A_847), B_846) | ~r1_tarski(A_847, B_846))), inference(superposition, [status(thm), theory('equality')], [c_1421, c_4979])).
% 35.44/25.70  tff(c_66346, plain, (![A_7, B_8]: (k4_subset_1(A_7, k3_subset_1(A_7, k4_xboole_0(A_7, B_8)), k4_xboole_0(A_7, B_8))=A_7 | ~r1_tarski(k3_xboole_0(A_7, B_8), A_7) | ~r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_4636, c_66322])).
% 35.44/25.70  tff(c_76606, plain, (![A_916, B_917]: (k4_subset_1(A_916, k3_xboole_0(A_916, B_917), k4_xboole_0(A_916, B_917))=A_916)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_387, c_4636, c_66346])).
% 35.44/25.70  tff(c_76975, plain, (![B_85, A_84]: (k4_subset_1(B_85, k3_xboole_0(A_84, B_85), k4_xboole_0(B_85, A_84))=B_85)), inference(superposition, [status(thm), theory('equality')], [c_246, c_76606])).
% 35.44/25.70  tff(c_89287, plain, (k4_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2')), k1_xboole_0)=k2_pre_topc('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89270, c_76975])).
% 35.44/25.70  tff(c_89466, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52395, c_22433, c_89287])).
% 35.44/25.70  tff(c_89468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2970, c_89466])).
% 35.44/25.70  tff(c_89469, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 35.44/25.70  tff(c_89633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89469, c_137])).
% 35.44/25.70  tff(c_89634, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 35.44/25.70  tff(c_89752, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89634, c_66])).
% 35.44/25.70  tff(c_91764, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91492, c_89752])).
% 35.44/25.70  tff(c_130650, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93653, c_91764])).
% 35.44/25.70  tff(c_92468, plain, (![A_1189, B_1190]: (k2_pre_topc(A_1189, B_1190)=B_1190 | ~v4_pre_topc(B_1190, A_1189) | ~m1_subset_1(B_1190, k1_zfmisc_1(u1_struct_0(A_1189))) | ~l1_pre_topc(A_1189))), inference(cnfTransformation, [status(thm)], [f_108])).
% 35.44/25.70  tff(c_92482, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_92468])).
% 35.44/25.70  tff(c_92488, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_89634, c_92482])).
% 35.44/25.70  tff(c_93817, plain, (![A_1232, B_1233]: (k4_subset_1(u1_struct_0(A_1232), B_1233, k2_tops_1(A_1232, B_1233))=k2_pre_topc(A_1232, B_1233) | ~m1_subset_1(B_1233, k1_zfmisc_1(u1_struct_0(A_1232))) | ~l1_pre_topc(A_1232))), inference(cnfTransformation, [status(thm)], [f_136])).
% 35.44/25.70  tff(c_93827, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_93817])).
% 35.44/25.70  tff(c_93833, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_92488, c_93827])).
% 35.44/25.70  tff(c_50, plain, (![A_48, B_49]: (m1_subset_1(k2_tops_1(A_48, B_49), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_114])).
% 35.44/25.70  tff(c_92575, plain, (![A_1194, B_1195, C_1196]: (k4_subset_1(A_1194, B_1195, C_1196)=k2_xboole_0(B_1195, C_1196) | ~m1_subset_1(C_1196, k1_zfmisc_1(A_1194)) | ~m1_subset_1(B_1195, k1_zfmisc_1(A_1194)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 35.44/25.70  tff(c_123648, plain, (![A_1597, B_1598, B_1599]: (k4_subset_1(u1_struct_0(A_1597), B_1598, k2_tops_1(A_1597, B_1599))=k2_xboole_0(B_1598, k2_tops_1(A_1597, B_1599)) | ~m1_subset_1(B_1598, k1_zfmisc_1(u1_struct_0(A_1597))) | ~m1_subset_1(B_1599, k1_zfmisc_1(u1_struct_0(A_1597))) | ~l1_pre_topc(A_1597))), inference(resolution, [status(thm)], [c_50, c_92575])).
% 35.44/25.70  tff(c_123664, plain, (![B_1599]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_1599))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_1599)) | ~m1_subset_1(B_1599, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_123648])).
% 35.44/25.70  tff(c_155927, plain, (![B_1856]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_1856))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_1856)) | ~m1_subset_1(B_1856, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_123664])).
% 35.44/25.70  tff(c_155950, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_155927])).
% 35.44/25.70  tff(c_155959, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_93833, c_155950])).
% 35.44/25.70  tff(c_89789, plain, (![A_1041, B_1042]: (k4_xboole_0(A_1041, k4_xboole_0(A_1041, B_1042))=k3_xboole_0(A_1041, B_1042))), inference(cnfTransformation, [status(thm)], [f_53])).
% 35.44/25.70  tff(c_89810, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89789])).
% 35.44/25.70  tff(c_89814, plain, (![A_1043]: (k4_xboole_0(A_1043, A_1043)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_89810])).
% 35.44/25.70  tff(c_89819, plain, (![A_1043]: (k4_xboole_0(A_1043, k1_xboole_0)=k3_xboole_0(A_1043, A_1043))), inference(superposition, [status(thm), theory('equality')], [c_89814, c_18])).
% 35.44/25.70  tff(c_89837, plain, (![A_1043]: (k3_xboole_0(A_1043, A_1043)=A_1043)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89819])).
% 35.44/25.70  tff(c_89661, plain, (![A_1032, B_1033]: (k3_tarski(k2_tarski(A_1032, B_1033))=k2_xboole_0(A_1032, B_1033))), inference(cnfTransformation, [status(thm)], [f_59])).
% 35.44/25.70  tff(c_90065, plain, (![B_1058, A_1059]: (k3_tarski(k2_tarski(B_1058, A_1059))=k2_xboole_0(A_1059, B_1058))), inference(superposition, [status(thm), theory('equality')], [c_22, c_89661])).
% 35.44/25.70  tff(c_90071, plain, (![B_1058, A_1059]: (k2_xboole_0(B_1058, A_1059)=k2_xboole_0(A_1059, B_1058))), inference(superposition, [status(thm), theory('equality')], [c_90065, c_24])).
% 35.44/25.70  tff(c_90129, plain, (![A_1062, C_1063, B_1064]: (r1_tarski(A_1062, C_1063) | ~r1_tarski(B_1064, C_1063) | ~r1_tarski(A_1062, B_1064))), inference(cnfTransformation, [status(thm)], [f_33])).
% 35.44/25.70  tff(c_90178, plain, (![A_1068, A_1069, B_1070]: (r1_tarski(A_1068, A_1069) | ~r1_tarski(A_1068, k4_xboole_0(A_1069, B_1070)))), inference(resolution, [status(thm)], [c_8, c_90129])).
% 35.44/25.70  tff(c_90217, plain, (![A_1069, B_1070, B_8]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_1069, B_1070), B_8), A_1069))), inference(resolution, [status(thm)], [c_8, c_90178])).
% 35.44/25.70  tff(c_90461, plain, (![A_1085, B_1086, C_1087]: (r1_tarski(A_1085, k2_xboole_0(B_1086, C_1087)) | ~r1_tarski(k4_xboole_0(A_1085, B_1086), C_1087))), inference(cnfTransformation, [status(thm)], [f_51])).
% 35.44/25.70  tff(c_90596, plain, (![A_1096, B_1097, B_1098]: (r1_tarski(k4_xboole_0(A_1096, B_1097), k2_xboole_0(B_1098, A_1096)))), inference(resolution, [status(thm)], [c_90217, c_90461])).
% 35.44/25.70  tff(c_90699, plain, (![A_1104, B_1105, B_1106]: (r1_tarski(A_1104, k2_xboole_0(B_1105, k2_xboole_0(B_1106, A_1104))))), inference(resolution, [status(thm)], [c_90596, c_16])).
% 35.44/25.70  tff(c_90721, plain, (![A_1104, B_1106, B_1058]: (r1_tarski(A_1104, k2_xboole_0(k2_xboole_0(B_1106, A_1104), B_1058)))), inference(superposition, [status(thm), theory('equality')], [c_90071, c_90699])).
% 35.44/25.70  tff(c_91280, plain, (![A_1141, B_1142, C_1143]: (r1_tarski(k4_xboole_0(A_1141, B_1142), C_1143) | ~r1_tarski(A_1141, k2_xboole_0(B_1142, C_1143)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 35.44/25.70  tff(c_100561, plain, (![A_1390, B_1391, B_1392]: (k4_xboole_0(A_1390, B_1391)=k1_xboole_0 | ~r1_tarski(A_1390, k2_xboole_0(B_1391, k4_xboole_0(B_1392, k4_xboole_0(A_1390, B_1391)))))), inference(resolution, [status(thm)], [c_91280, c_10])).
% 35.44/25.70  tff(c_101849, plain, (![A_1403, B_1404]: (k4_xboole_0(A_1403, k2_xboole_0(B_1404, A_1403))=k1_xboole_0)), inference(resolution, [status(thm)], [c_90721, c_100561])).
% 35.44/25.70  tff(c_102022, plain, (![A_1403, B_1404]: (k3_xboole_0(A_1403, k2_xboole_0(B_1404, A_1403))=k4_xboole_0(A_1403, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_101849, c_18])).
% 35.44/25.70  tff(c_102107, plain, (![A_1403, B_1404]: (k3_xboole_0(A_1403, k2_xboole_0(B_1404, A_1403))=A_1403)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_102022])).
% 35.44/25.70  tff(c_89641, plain, (![A_1028, B_1029]: (k1_setfam_1(k2_tarski(A_1028, B_1029))=k3_xboole_0(A_1028, B_1029))), inference(cnfTransformation, [status(thm)], [f_89])).
% 35.44/25.70  tff(c_89681, plain, (![A_1036, B_1037]: (k1_setfam_1(k2_tarski(A_1036, B_1037))=k3_xboole_0(B_1037, A_1036))), inference(superposition, [status(thm), theory('equality')], [c_22, c_89641])).
% 35.44/25.70  tff(c_89687, plain, (![B_1037, A_1036]: (k3_xboole_0(B_1037, A_1036)=k3_xboole_0(A_1036, B_1037))), inference(superposition, [status(thm), theory('equality')], [c_89681, c_40])).
% 35.44/25.70  tff(c_89825, plain, (![A_1043]: (r1_tarski(k1_xboole_0, A_1043))), inference(superposition, [status(thm), theory('equality')], [c_89814, c_8])).
% 35.44/25.70  tff(c_90690, plain, (![A_1102, B_1103]: (k4_xboole_0(A_1102, B_1103)=k3_subset_1(A_1102, B_1103) | ~m1_subset_1(B_1103, k1_zfmisc_1(A_1102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 35.44/25.70  tff(c_94172, plain, (![B_1242, A_1243]: (k4_xboole_0(B_1242, A_1243)=k3_subset_1(B_1242, A_1243) | ~r1_tarski(A_1243, B_1242))), inference(resolution, [status(thm)], [c_44, c_90690])).
% 35.44/25.70  tff(c_94370, plain, (![A_1043]: (k4_xboole_0(A_1043, k1_xboole_0)=k3_subset_1(A_1043, k1_xboole_0))), inference(resolution, [status(thm)], [c_89825, c_94172])).
% 35.44/25.70  tff(c_94447, plain, (![A_1043]: (k3_subset_1(A_1043, k1_xboole_0)=A_1043)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_94370])).
% 35.44/25.70  tff(c_91493, plain, (![A_1158, C_1159]: (r1_tarski(A_1158, C_1159) | ~r1_tarski(A_1158, k2_xboole_0(k1_xboole_0, C_1159)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_91280])).
% 35.44/25.70  tff(c_91820, plain, (![C_1163, B_1164]: (r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0, C_1163), B_1164), C_1163))), inference(resolution, [status(thm)], [c_8, c_91493])).
% 35.44/25.70  tff(c_92138, plain, (![C_1175, B_1176]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_1175), k2_xboole_0(B_1176, C_1175)))), inference(resolution, [status(thm)], [c_91820, c_16])).
% 35.44/25.70  tff(c_92166, plain, (![A_1059, B_1058]: (r1_tarski(k2_xboole_0(k1_xboole_0, A_1059), k2_xboole_0(A_1059, B_1058)))), inference(superposition, [status(thm), theory('equality')], [c_90071, c_92138])).
% 35.44/25.70  tff(c_100744, plain, (![A_1393]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, A_1393), A_1393)=k1_xboole_0)), inference(resolution, [status(thm)], [c_92166, c_100561])).
% 35.44/25.70  tff(c_94379, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_94172])).
% 35.44/25.70  tff(c_94453, plain, (![A_7, B_8]: (k3_subset_1(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_94379])).
% 35.44/25.70  tff(c_100797, plain, (![A_1393]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, A_1393), A_1393)=k3_subset_1(k2_xboole_0(k1_xboole_0, A_1393), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_100744, c_94453])).
% 35.44/25.70  tff(c_116611, plain, (![A_1524]: (k3_xboole_0(k2_xboole_0(k1_xboole_0, A_1524), A_1524)=k2_xboole_0(k1_xboole_0, A_1524))), inference(demodulation, [status(thm), theory('equality')], [c_94447, c_100797])).
% 35.44/25.70  tff(c_116839, plain, (![A_1524]: (k3_xboole_0(A_1524, k2_xboole_0(k1_xboole_0, A_1524))=k2_xboole_0(k1_xboole_0, A_1524))), inference(superposition, [status(thm), theory('equality')], [c_116611, c_89687])).
% 35.44/25.70  tff(c_117012, plain, (![A_1525]: (k2_xboole_0(k1_xboole_0, A_1525)=A_1525)), inference(demodulation, [status(thm), theory('equality')], [c_102107, c_116839])).
% 35.44/25.70  tff(c_117302, plain, (![A_1059]: (k2_xboole_0(A_1059, k1_xboole_0)=A_1059)), inference(superposition, [status(thm), theory('equality')], [c_90071, c_117012])).
% 35.44/25.70  tff(c_90606, plain, (![B_1058, B_1097, A_1059]: (r1_tarski(k4_xboole_0(B_1058, B_1097), k2_xboole_0(B_1058, A_1059)))), inference(superposition, [status(thm), theory('equality')], [c_90071, c_90596])).
% 35.44/25.70  tff(c_100912, plain, (![B_1394, B_1395]: (k4_xboole_0(k4_xboole_0(B_1394, B_1395), B_1394)=k1_xboole_0)), inference(resolution, [status(thm)], [c_90606, c_100561])).
% 35.44/25.70  tff(c_101321, plain, (![A_1396, B_1397]: (k4_xboole_0(k3_xboole_0(A_1396, B_1397), A_1396)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_100912])).
% 35.44/25.70  tff(c_101431, plain, (![A_1036, B_1037]: (k4_xboole_0(k3_xboole_0(A_1036, B_1037), B_1037)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89687, c_101321])).
% 35.44/25.70  tff(c_90498, plain, (![A_1085, B_1086]: (r1_tarski(A_1085, k2_xboole_0(B_1086, k4_xboole_0(A_1085, B_1086))))), inference(resolution, [status(thm)], [c_102, c_90461])).
% 35.44/25.70  tff(c_90500, plain, (![A_1088, B_1089]: (r1_tarski(A_1088, k2_xboole_0(B_1089, A_1088)))), inference(resolution, [status(thm)], [c_8, c_90461])).
% 35.44/25.70  tff(c_92814, plain, (![A_1203, B_1204, A_1205]: (r1_tarski(A_1203, k2_xboole_0(B_1204, A_1205)) | ~r1_tarski(A_1203, A_1205))), inference(resolution, [status(thm)], [c_90500, c_4])).
% 35.44/25.70  tff(c_92835, plain, (![A_1203, A_1059, B_1058]: (r1_tarski(A_1203, k2_xboole_0(A_1059, B_1058)) | ~r1_tarski(A_1203, A_1059))), inference(superposition, [status(thm), theory('equality')], [c_90071, c_92814])).
% 35.44/25.70  tff(c_103298, plain, (![A_1417, A_1418]: (k4_xboole_0(A_1417, A_1418)=k1_xboole_0 | ~r1_tarski(A_1417, A_1418))), inference(resolution, [status(thm)], [c_92835, c_100561])).
% 35.44/25.70  tff(c_113350, plain, (![A_1501, B_1502]: (k4_xboole_0(A_1501, k2_xboole_0(B_1502, k4_xboole_0(A_1501, B_1502)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_90498, c_103298])).
% 35.44/25.70  tff(c_113505, plain, (![A_1501, B_1502]: (k3_xboole_0(A_1501, k2_xboole_0(B_1502, k4_xboole_0(A_1501, B_1502)))=k3_subset_1(A_1501, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113350, c_94453])).
% 35.44/25.70  tff(c_118378, plain, (![A_1540, B_1541]: (k3_xboole_0(A_1540, k2_xboole_0(B_1541, k4_xboole_0(A_1540, B_1541)))=A_1540)), inference(demodulation, [status(thm), theory('equality')], [c_94447, c_113505])).
% 35.44/25.70  tff(c_118698, plain, (![A_1036, B_1037]: (k3_xboole_0(k3_xboole_0(A_1036, B_1037), k2_xboole_0(B_1037, k1_xboole_0))=k3_xboole_0(A_1036, B_1037))), inference(superposition, [status(thm), theory('equality')], [c_101431, c_118378])).
% 35.44/25.70  tff(c_133445, plain, (![B_1684, A_1685]: (k3_xboole_0(B_1684, k3_xboole_0(A_1685, B_1684))=k3_xboole_0(A_1685, B_1684))), inference(demodulation, [status(thm), theory('equality')], [c_89687, c_117302, c_118698])).
% 35.44/25.70  tff(c_134092, plain, (![A_1687, B_1688]: (k3_xboole_0(A_1687, k3_xboole_0(A_1687, B_1688))=k3_xboole_0(B_1688, A_1687))), inference(superposition, [status(thm), theory('equality')], [c_89687, c_133445])).
% 35.44/25.70  tff(c_134481, plain, (![B_1404, A_1403]: (k3_xboole_0(k2_xboole_0(B_1404, A_1403), A_1403)=k3_xboole_0(A_1403, A_1403))), inference(superposition, [status(thm), theory('equality')], [c_102107, c_134092])).
% 35.44/25.70  tff(c_134598, plain, (![B_1404, A_1403]: (k3_xboole_0(k2_xboole_0(B_1404, A_1403), A_1403)=A_1403)), inference(demodulation, [status(thm), theory('equality')], [c_89837, c_134481])).
% 35.44/25.70  tff(c_156028, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_155959, c_134598])).
% 35.44/25.70  tff(c_156185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130650, c_156028])).
% 35.44/25.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.44/25.70  
% 35.44/25.70  Inference rules
% 35.44/25.70  ----------------------
% 35.44/25.70  #Ref     : 0
% 35.44/25.70  #Sup     : 36947
% 35.44/25.70  #Fact    : 0
% 35.44/25.70  #Define  : 0
% 35.44/25.70  #Split   : 20
% 35.44/25.70  #Chain   : 0
% 35.44/25.70  #Close   : 0
% 35.44/25.70  
% 35.44/25.70  Ordering : KBO
% 35.44/25.70  
% 35.44/25.70  Simplification rules
% 35.44/25.70  ----------------------
% 35.44/25.70  #Subsume      : 2327
% 35.44/25.70  #Demod        : 41541
% 35.44/25.70  #Tautology    : 23533
% 35.44/25.70  #SimpNegUnit  : 18
% 35.44/25.70  #BackRed      : 99
% 35.44/25.70  
% 35.44/25.70  #Partial instantiations: 0
% 35.44/25.70  #Strategies tried      : 1
% 35.44/25.70  
% 35.44/25.70  Timing (in seconds)
% 35.44/25.70  ----------------------
% 35.44/25.71  Preprocessing        : 0.44
% 35.44/25.71  Parsing              : 0.23
% 35.44/25.71  CNF conversion       : 0.03
% 35.44/25.71  Main loop            : 24.36
% 35.44/25.71  Inferencing          : 2.85
% 35.44/25.71  Reduction            : 14.99
% 35.44/25.71  Demodulation         : 13.48
% 35.44/25.71  BG Simplification    : 0.28
% 35.44/25.71  Subsumption          : 5.24
% 35.44/25.71  Abstraction          : 0.53
% 35.44/25.71  MUC search           : 0.00
% 35.44/25.71  Cooper               : 0.00
% 35.44/25.71  Total                : 24.88
% 35.44/25.71  Index Insertion      : 0.00
% 35.44/25.71  Index Deletion       : 0.00
% 35.44/25.71  Index Matching       : 0.00
% 35.44/25.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
