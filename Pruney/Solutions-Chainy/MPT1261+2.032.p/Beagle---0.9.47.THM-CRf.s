%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:16 EST 2020

% Result     : Theorem 31.92s
% Output     : CNFRefutation 31.98s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 447 expanded)
%              Number of leaves         :   50 ( 170 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 862 expanded)
%              Number of equality atoms :   91 ( 266 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_112,axiom,(
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

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_71,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_115070,plain,(
    ! [A_1323,B_1324,C_1325] :
      ( k7_subset_1(A_1323,B_1324,C_1325) = k4_xboole_0(B_1324,C_1325)
      | ~ m1_subset_1(B_1324,k1_zfmisc_1(A_1323)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_115098,plain,(
    ! [C_1325] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1325) = k4_xboole_0('#skF_2',C_1325) ),
    inference(resolution,[status(thm)],[c_64,c_115070])).

tff(c_70,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_212,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3631,plain,(
    ! [B_264,A_265] :
      ( v4_pre_topc(B_264,A_265)
      | k2_pre_topc(A_265,B_264) != B_264
      | ~ v2_pre_topc(A_265)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3668,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_3631])).

tff(c_3682,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_3668])).

tff(c_3683,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_3682])).

tff(c_76,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_118,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_2488,plain,(
    ! [A_208,B_209,C_210] :
      ( k7_subset_1(A_208,B_209,C_210) = k4_xboole_0(B_209,C_210)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2603,plain,(
    ! [C_217] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_217) = k4_xboole_0('#skF_2',C_217) ),
    inference(resolution,[status(thm)],[c_64,c_2488])).

tff(c_2615,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_2603])).

tff(c_2513,plain,(
    ! [C_210] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_210) = k4_xboole_0('#skF_2',C_210) ),
    inference(resolution,[status(thm)],[c_64,c_2488])).

tff(c_4096,plain,(
    ! [A_278,B_279] :
      ( k7_subset_1(u1_struct_0(A_278),B_279,k2_tops_1(A_278,B_279)) = k1_tops_1(A_278,B_279)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4125,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_4096])).

tff(c_4144,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2513,c_4125])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4202,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4144,c_18])).

tff(c_4215,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_4202])).

tff(c_292,plain,(
    ! [A_96,B_97] : k4_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_307,plain,(
    ! [A_96,B_97] : r1_tarski(k3_xboole_0(A_96,B_97),A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_8])).

tff(c_48,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_31,B_32] : m1_subset_1(k6_subset_1(A_31,B_32),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,(
    ! [A_31,B_32] : m1_subset_1(k4_xboole_0(A_31,B_32),k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_3130,plain,(
    ! [A_239,B_240,C_241] :
      ( k4_subset_1(A_239,B_240,C_241) = k2_xboole_0(B_240,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(A_239))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24235,plain,(
    ! [A_524,B_525,B_526] :
      ( k4_subset_1(A_524,B_525,k4_xboole_0(A_524,B_526)) = k2_xboole_0(B_525,k4_xboole_0(A_524,B_526))
      | ~ m1_subset_1(B_525,k1_zfmisc_1(A_524)) ) ),
    inference(resolution,[status(thm)],[c_77,c_3130])).

tff(c_108640,plain,(
    ! [B_1167,A_1168,B_1169] :
      ( k4_subset_1(B_1167,A_1168,k4_xboole_0(B_1167,B_1169)) = k2_xboole_0(A_1168,k4_xboole_0(B_1167,B_1169))
      | ~ r1_tarski(A_1168,B_1167) ) ),
    inference(resolution,[status(thm)],[c_48,c_24235])).

tff(c_1437,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(A_166,B_167) = k3_subset_1(A_166,B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1458,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_subset_1(A_31,k4_xboole_0(A_31,B_32)) ),
    inference(resolution,[status(thm)],[c_77,c_1437])).

tff(c_1471,plain,(
    ! [A_31,B_32] : k3_subset_1(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1458])).

tff(c_1694,plain,(
    ! [A_173,B_174] :
      ( k3_subset_1(A_173,k3_subset_1(A_173,B_174)) = B_174
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1719,plain,(
    ! [A_31,B_32] : k3_subset_1(A_31,k3_subset_1(A_31,k4_xboole_0(A_31,B_32))) = k4_xboole_0(A_31,B_32) ),
    inference(resolution,[status(thm)],[c_77,c_1694])).

tff(c_5188,plain,(
    ! [A_31,B_32] : k3_subset_1(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1719])).

tff(c_26,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_43,B_44] :
      ( k4_subset_1(A_43,B_44,k3_subset_1(A_43,B_44)) = k2_subset_1(A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2210,plain,(
    ! [A_195,B_196] :
      ( k4_subset_1(A_195,B_196,k3_subset_1(A_195,B_196)) = A_195
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_195)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_6503,plain,(
    ! [B_323,A_324] :
      ( k4_subset_1(B_323,A_324,k3_subset_1(B_323,A_324)) = B_323
      | ~ r1_tarski(A_324,B_323) ) ),
    inference(resolution,[status(thm)],[c_48,c_2210])).

tff(c_6518,plain,(
    ! [A_31,B_32] :
      ( k4_subset_1(A_31,k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31
      | ~ r1_tarski(k3_xboole_0(A_31,B_32),A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5188,c_6503])).

tff(c_6545,plain,(
    ! [A_31,B_32] : k4_subset_1(A_31,k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_6518])).

tff(c_108675,plain,(
    ! [B_1167,B_1169] :
      ( k2_xboole_0(k3_xboole_0(B_1167,B_1169),k4_xboole_0(B_1167,B_1169)) = B_1167
      | ~ r1_tarski(k3_xboole_0(B_1167,B_1169),B_1167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108640,c_6545])).

tff(c_108974,plain,(
    ! [B_1167,B_1169] : k2_xboole_0(k3_xboole_0(B_1167,B_1169),k4_xboole_0(B_1167,B_1169)) = B_1167 ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_108675])).

tff(c_22,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_192,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_213,plain,(
    ! [A_90,B_91] : k3_tarski(k2_tarski(A_90,B_91)) = k2_xboole_0(B_91,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_192])).

tff(c_24,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_219,plain,(
    ! [B_91,A_90] : k2_xboole_0(B_91,A_90) = k2_xboole_0(A_90,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_24])).

tff(c_109075,plain,(
    ! [B_1170,B_1171] : k2_xboole_0(k3_xboole_0(B_1170,B_1171),k4_xboole_0(B_1170,B_1171)) = B_1170 ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_108675])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109337,plain,(
    ! [B_1170,B_1171] : k2_xboole_0(k3_xboole_0(B_1170,B_1171),k4_xboole_0(B_1170,B_1171)) = k2_xboole_0(k3_xboole_0(B_1170,B_1171),B_1170) ),
    inference(superposition,[status(thm),theory(equality)],[c_109075,c_20])).

tff(c_109904,plain,(
    ! [B_1172,B_1173] : k2_xboole_0(B_1172,k3_xboole_0(B_1172,B_1173)) = B_1172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108974,c_219,c_109337])).

tff(c_110532,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4215,c_109904])).

tff(c_3789,plain,(
    ! [A_269,B_270] :
      ( k4_subset_1(u1_struct_0(A_269),B_270,k2_tops_1(A_269,B_270)) = k2_pre_topc(A_269,B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3818,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_3789])).

tff(c_3835,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3818])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_70,B_71] : r1_tarski(k4_xboole_0(A_70,B_71),A_70) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_104])).

tff(c_3041,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2615,c_8])).

tff(c_177,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(A_84,B_85)
      | ~ m1_subset_1(A_84,k1_zfmisc_1(B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_191,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_177])).

tff(c_701,plain,(
    ! [A_119,C_120,B_121] :
      ( r1_tarski(A_119,C_120)
      | ~ r1_tarski(B_121,C_120)
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_773,plain,(
    ! [A_126] :
      ( r1_tarski(A_126,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_126,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_191,c_701])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_776,plain,(
    ! [A_3,A_126] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_126)
      | ~ r1_tarski(A_126,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_773,c_4])).

tff(c_3046,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_3041,c_776])).

tff(c_3051,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_3046])).

tff(c_16853,plain,(
    ! [B_460,B_461,A_462] :
      ( k4_subset_1(B_460,B_461,A_462) = k2_xboole_0(B_461,A_462)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(B_460))
      | ~ r1_tarski(A_462,B_460) ) ),
    inference(resolution,[status(thm)],[c_48,c_3130])).

tff(c_17509,plain,(
    ! [A_467] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_467) = k2_xboole_0('#skF_2',A_467)
      | ~ r1_tarski(A_467,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_64,c_16853])).

tff(c_17616,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3051,c_17509])).

tff(c_17774,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3835,c_17616])).

tff(c_112899,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110532,c_17774])).

tff(c_112901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3683,c_112899])).

tff(c_112902,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_113162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112902,c_118])).

tff(c_113163,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_113259,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113163,c_70])).

tff(c_115126,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115098,c_113259])).

tff(c_115957,plain,(
    ! [A_1362,B_1363] :
      ( r1_tarski(k2_tops_1(A_1362,B_1363),B_1363)
      | ~ v4_pre_topc(B_1363,A_1362)
      | ~ m1_subset_1(B_1363,k1_zfmisc_1(u1_struct_0(A_1362)))
      | ~ l1_pre_topc(A_1362) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_115984,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_115957])).

tff(c_115998,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_113163,c_115984])).

tff(c_116949,plain,(
    ! [A_1393,B_1394] :
      ( k7_subset_1(u1_struct_0(A_1393),B_1394,k2_tops_1(A_1393,B_1394)) = k1_tops_1(A_1393,B_1394)
      | ~ m1_subset_1(B_1394,k1_zfmisc_1(u1_struct_0(A_1393)))
      | ~ l1_pre_topc(A_1393) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_116978,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_116949])).

tff(c_116997,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_115098,c_116978])).

tff(c_114638,plain,(
    ! [A_1301,B_1302] :
      ( k4_xboole_0(A_1301,B_1302) = k3_subset_1(A_1301,B_1302)
      | ~ m1_subset_1(B_1302,k1_zfmisc_1(A_1301)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117475,plain,(
    ! [B_1410,A_1411] :
      ( k4_xboole_0(B_1410,A_1411) = k3_subset_1(B_1410,A_1411)
      | ~ r1_tarski(A_1411,B_1410) ) ),
    inference(resolution,[status(thm)],[c_48,c_114638])).

tff(c_117556,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_115998,c_117475])).

tff(c_117701,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116997,c_117556])).

tff(c_114494,plain,(
    ! [A_1291,B_1292] :
      ( k3_subset_1(A_1291,k3_subset_1(A_1291,B_1292)) = B_1292
      | ~ m1_subset_1(B_1292,k1_zfmisc_1(A_1291)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_117983,plain,(
    ! [B_1415,A_1416] :
      ( k3_subset_1(B_1415,k3_subset_1(B_1415,A_1416)) = A_1416
      | ~ r1_tarski(A_1416,B_1415) ) ),
    inference(resolution,[status(thm)],[c_48,c_114494])).

tff(c_118007,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_117701,c_117983])).

tff(c_118031,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115998,c_118007])).

tff(c_117070,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116997,c_77])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k3_subset_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119259,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118031,c_30])).

tff(c_119269,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117070,c_119259])).

tff(c_129702,plain,(
    ! [A_1596,B_1597] :
      ( k4_xboole_0(A_1596,k3_subset_1(A_1596,B_1597)) = k3_subset_1(A_1596,k3_subset_1(A_1596,B_1597))
      | ~ m1_subset_1(B_1597,k1_zfmisc_1(A_1596)) ) ),
    inference(resolution,[status(thm)],[c_30,c_114638])).

tff(c_129710,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_119269,c_129702])).

tff(c_129739,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118031,c_117701,c_117701,c_129710])).

tff(c_129741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115126,c_129739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:54:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.92/22.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.98/22.89  
% 31.98/22.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.98/22.89  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 31.98/22.89  
% 31.98/22.89  %Foreground sorts:
% 31.98/22.89  
% 31.98/22.89  
% 31.98/22.89  %Background operators:
% 31.98/22.89  
% 31.98/22.89  
% 31.98/22.89  %Foreground operators:
% 31.98/22.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.98/22.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 31.98/22.89  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 31.98/22.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.98/22.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 31.98/22.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 31.98/22.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.98/22.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 31.98/22.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 31.98/22.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 31.98/22.89  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 31.98/22.89  tff('#skF_2', type, '#skF_2': $i).
% 31.98/22.89  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 31.98/22.89  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 31.98/22.89  tff('#skF_1', type, '#skF_1': $i).
% 31.98/22.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.98/22.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 31.98/22.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.98/22.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 31.98/22.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.98/22.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 31.98/22.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.98/22.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 31.98/22.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 31.98/22.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 31.98/22.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 31.98/22.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.98/22.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 31.98/22.89  
% 31.98/22.91  tff(f_160, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 31.98/22.91  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 31.98/22.91  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 31.98/22.91  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 31.98/22.91  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 31.98/22.91  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 31.98/22.91  tff(f_97, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 31.98/22.91  tff(f_83, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 31.98/22.91  tff(f_71, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 31.98/22.91  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 31.98/22.91  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 31.98/22.91  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 31.98/22.91  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 31.98/22.91  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 31.98/22.91  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 31.98/22.91  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 31.98/22.91  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 31.98/22.91  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 31.98/22.91  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 31.98/22.91  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 31.98/22.91  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 31.98/22.91  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 31.98/22.91  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.98/22.91  tff(c_115070, plain, (![A_1323, B_1324, C_1325]: (k7_subset_1(A_1323, B_1324, C_1325)=k4_xboole_0(B_1324, C_1325) | ~m1_subset_1(B_1324, k1_zfmisc_1(A_1323)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 31.98/22.91  tff(c_115098, plain, (![C_1325]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1325)=k4_xboole_0('#skF_2', C_1325))), inference(resolution, [status(thm)], [c_64, c_115070])).
% 31.98/22.91  tff(c_70, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.98/22.91  tff(c_212, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 31.98/22.91  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.98/22.91  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.98/22.91  tff(c_3631, plain, (![B_264, A_265]: (v4_pre_topc(B_264, A_265) | k2_pre_topc(A_265, B_264)!=B_264 | ~v2_pre_topc(A_265) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.98/22.91  tff(c_3668, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_3631])).
% 31.98/22.91  tff(c_3682, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_3668])).
% 31.98/22.91  tff(c_3683, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_212, c_3682])).
% 31.98/22.91  tff(c_76, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 31.98/22.91  tff(c_118, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_76])).
% 31.98/22.91  tff(c_2488, plain, (![A_208, B_209, C_210]: (k7_subset_1(A_208, B_209, C_210)=k4_xboole_0(B_209, C_210) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 31.98/22.91  tff(c_2603, plain, (![C_217]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_217)=k4_xboole_0('#skF_2', C_217))), inference(resolution, [status(thm)], [c_64, c_2488])).
% 31.98/22.91  tff(c_2615, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_2603])).
% 31.98/22.91  tff(c_2513, plain, (![C_210]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_210)=k4_xboole_0('#skF_2', C_210))), inference(resolution, [status(thm)], [c_64, c_2488])).
% 31.98/22.91  tff(c_4096, plain, (![A_278, B_279]: (k7_subset_1(u1_struct_0(A_278), B_279, k2_tops_1(A_278, B_279))=k1_tops_1(A_278, B_279) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_148])).
% 31.98/22.91  tff(c_4125, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_4096])).
% 31.98/22.91  tff(c_4144, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2513, c_4125])).
% 31.98/22.91  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 31.98/22.91  tff(c_4202, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4144, c_18])).
% 31.98/22.91  tff(c_4215, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_4202])).
% 31.98/22.91  tff(c_292, plain, (![A_96, B_97]: (k4_xboole_0(A_96, k4_xboole_0(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 31.98/22.91  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.98/22.91  tff(c_307, plain, (![A_96, B_97]: (r1_tarski(k3_xboole_0(A_96, B_97), A_96))), inference(superposition, [status(thm), theory('equality')], [c_292, c_8])).
% 31.98/22.91  tff(c_48, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_97])).
% 31.98/22.91  tff(c_38, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_83])).
% 31.98/22.91  tff(c_32, plain, (![A_31, B_32]: (m1_subset_1(k6_subset_1(A_31, B_32), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 31.98/22.91  tff(c_77, plain, (![A_31, B_32]: (m1_subset_1(k4_xboole_0(A_31, B_32), k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 31.98/22.91  tff(c_3130, plain, (![A_239, B_240, C_241]: (k4_subset_1(A_239, B_240, C_241)=k2_xboole_0(B_240, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(A_239)) | ~m1_subset_1(B_240, k1_zfmisc_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 31.98/22.91  tff(c_24235, plain, (![A_524, B_525, B_526]: (k4_subset_1(A_524, B_525, k4_xboole_0(A_524, B_526))=k2_xboole_0(B_525, k4_xboole_0(A_524, B_526)) | ~m1_subset_1(B_525, k1_zfmisc_1(A_524)))), inference(resolution, [status(thm)], [c_77, c_3130])).
% 31.98/22.91  tff(c_108640, plain, (![B_1167, A_1168, B_1169]: (k4_subset_1(B_1167, A_1168, k4_xboole_0(B_1167, B_1169))=k2_xboole_0(A_1168, k4_xboole_0(B_1167, B_1169)) | ~r1_tarski(A_1168, B_1167))), inference(resolution, [status(thm)], [c_48, c_24235])).
% 31.98/22.91  tff(c_1437, plain, (![A_166, B_167]: (k4_xboole_0(A_166, B_167)=k3_subset_1(A_166, B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 31.98/22.91  tff(c_1458, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_subset_1(A_31, k4_xboole_0(A_31, B_32)))), inference(resolution, [status(thm)], [c_77, c_1437])).
% 31.98/22.91  tff(c_1471, plain, (![A_31, B_32]: (k3_subset_1(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1458])).
% 31.98/22.91  tff(c_1694, plain, (![A_173, B_174]: (k3_subset_1(A_173, k3_subset_1(A_173, B_174))=B_174 | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 31.98/22.91  tff(c_1719, plain, (![A_31, B_32]: (k3_subset_1(A_31, k3_subset_1(A_31, k4_xboole_0(A_31, B_32)))=k4_xboole_0(A_31, B_32))), inference(resolution, [status(thm)], [c_77, c_1694])).
% 31.98/22.91  tff(c_5188, plain, (![A_31, B_32]: (k3_subset_1(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1719])).
% 31.98/22.91  tff(c_26, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.98/22.91  tff(c_42, plain, (![A_43, B_44]: (k4_subset_1(A_43, B_44, k3_subset_1(A_43, B_44))=k2_subset_1(A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 31.98/22.91  tff(c_2210, plain, (![A_195, B_196]: (k4_subset_1(A_195, B_196, k3_subset_1(A_195, B_196))=A_195 | ~m1_subset_1(B_196, k1_zfmisc_1(A_195)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_42])).
% 31.98/22.91  tff(c_6503, plain, (![B_323, A_324]: (k4_subset_1(B_323, A_324, k3_subset_1(B_323, A_324))=B_323 | ~r1_tarski(A_324, B_323))), inference(resolution, [status(thm)], [c_48, c_2210])).
% 31.98/22.91  tff(c_6518, plain, (![A_31, B_32]: (k4_subset_1(A_31, k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31 | ~r1_tarski(k3_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_5188, c_6503])).
% 31.98/22.91  tff(c_6545, plain, (![A_31, B_32]: (k4_subset_1(A_31, k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_307, c_6518])).
% 31.98/22.91  tff(c_108675, plain, (![B_1167, B_1169]: (k2_xboole_0(k3_xboole_0(B_1167, B_1169), k4_xboole_0(B_1167, B_1169))=B_1167 | ~r1_tarski(k3_xboole_0(B_1167, B_1169), B_1167))), inference(superposition, [status(thm), theory('equality')], [c_108640, c_6545])).
% 31.98/22.91  tff(c_108974, plain, (![B_1167, B_1169]: (k2_xboole_0(k3_xboole_0(B_1167, B_1169), k4_xboole_0(B_1167, B_1169))=B_1167)), inference(demodulation, [status(thm), theory('equality')], [c_307, c_108675])).
% 31.98/22.91  tff(c_22, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.98/22.91  tff(c_192, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 31.98/22.91  tff(c_213, plain, (![A_90, B_91]: (k3_tarski(k2_tarski(A_90, B_91))=k2_xboole_0(B_91, A_90))), inference(superposition, [status(thm), theory('equality')], [c_22, c_192])).
% 31.98/22.91  tff(c_24, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 31.98/22.91  tff(c_219, plain, (![B_91, A_90]: (k2_xboole_0(B_91, A_90)=k2_xboole_0(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_213, c_24])).
% 31.98/22.91  tff(c_109075, plain, (![B_1170, B_1171]: (k2_xboole_0(k3_xboole_0(B_1170, B_1171), k4_xboole_0(B_1170, B_1171))=B_1170)), inference(demodulation, [status(thm), theory('equality')], [c_307, c_108675])).
% 31.98/22.91  tff(c_20, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 31.98/22.91  tff(c_109337, plain, (![B_1170, B_1171]: (k2_xboole_0(k3_xboole_0(B_1170, B_1171), k4_xboole_0(B_1170, B_1171))=k2_xboole_0(k3_xboole_0(B_1170, B_1171), B_1170))), inference(superposition, [status(thm), theory('equality')], [c_109075, c_20])).
% 31.98/22.91  tff(c_109904, plain, (![B_1172, B_1173]: (k2_xboole_0(B_1172, k3_xboole_0(B_1172, B_1173))=B_1172)), inference(demodulation, [status(thm), theory('equality')], [c_108974, c_219, c_109337])).
% 31.98/22.91  tff(c_110532, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4215, c_109904])).
% 31.98/22.91  tff(c_3789, plain, (![A_269, B_270]: (k4_subset_1(u1_struct_0(A_269), B_270, k2_tops_1(A_269, B_270))=k2_pre_topc(A_269, B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_132])).
% 31.98/22.91  tff(c_3818, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_3789])).
% 31.98/22.91  tff(c_3835, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3818])).
% 31.98/22.91  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 31.98/22.91  tff(c_104, plain, (![A_70, B_71]: (r1_tarski(k4_xboole_0(A_70, B_71), A_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.98/22.91  tff(c_107, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_104])).
% 31.98/22.91  tff(c_3041, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2615, c_8])).
% 31.98/22.91  tff(c_177, plain, (![A_84, B_85]: (r1_tarski(A_84, B_85) | ~m1_subset_1(A_84, k1_zfmisc_1(B_85)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 31.98/22.91  tff(c_191, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_177])).
% 31.98/22.91  tff(c_701, plain, (![A_119, C_120, B_121]: (r1_tarski(A_119, C_120) | ~r1_tarski(B_121, C_120) | ~r1_tarski(A_119, B_121))), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.98/22.91  tff(c_773, plain, (![A_126]: (r1_tarski(A_126, u1_struct_0('#skF_1')) | ~r1_tarski(A_126, '#skF_2'))), inference(resolution, [status(thm)], [c_191, c_701])).
% 31.98/22.91  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 31.98/22.91  tff(c_776, plain, (![A_3, A_126]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_126) | ~r1_tarski(A_126, '#skF_2'))), inference(resolution, [status(thm)], [c_773, c_4])).
% 31.98/22.91  tff(c_3046, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_3041, c_776])).
% 31.98/22.91  tff(c_3051, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_3046])).
% 31.98/22.91  tff(c_16853, plain, (![B_460, B_461, A_462]: (k4_subset_1(B_460, B_461, A_462)=k2_xboole_0(B_461, A_462) | ~m1_subset_1(B_461, k1_zfmisc_1(B_460)) | ~r1_tarski(A_462, B_460))), inference(resolution, [status(thm)], [c_48, c_3130])).
% 31.98/22.91  tff(c_17509, plain, (![A_467]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_467)=k2_xboole_0('#skF_2', A_467) | ~r1_tarski(A_467, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_64, c_16853])).
% 31.98/22.91  tff(c_17616, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3051, c_17509])).
% 31.98/22.91  tff(c_17774, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3835, c_17616])).
% 31.98/22.91  tff(c_112899, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110532, c_17774])).
% 31.98/22.91  tff(c_112901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3683, c_112899])).
% 31.98/22.91  tff(c_112902, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 31.98/22.91  tff(c_113162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112902, c_118])).
% 31.98/22.91  tff(c_113163, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_76])).
% 31.98/22.91  tff(c_113259, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_113163, c_70])).
% 31.98/22.91  tff(c_115126, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115098, c_113259])).
% 31.98/22.91  tff(c_115957, plain, (![A_1362, B_1363]: (r1_tarski(k2_tops_1(A_1362, B_1363), B_1363) | ~v4_pre_topc(B_1363, A_1362) | ~m1_subset_1(B_1363, k1_zfmisc_1(u1_struct_0(A_1362))) | ~l1_pre_topc(A_1362))), inference(cnfTransformation, [status(thm)], [f_141])).
% 31.98/22.91  tff(c_115984, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_115957])).
% 31.98/22.91  tff(c_115998, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_113163, c_115984])).
% 31.98/22.91  tff(c_116949, plain, (![A_1393, B_1394]: (k7_subset_1(u1_struct_0(A_1393), B_1394, k2_tops_1(A_1393, B_1394))=k1_tops_1(A_1393, B_1394) | ~m1_subset_1(B_1394, k1_zfmisc_1(u1_struct_0(A_1393))) | ~l1_pre_topc(A_1393))), inference(cnfTransformation, [status(thm)], [f_148])).
% 31.98/22.91  tff(c_116978, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_116949])).
% 31.98/22.91  tff(c_116997, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_115098, c_116978])).
% 31.98/22.91  tff(c_114638, plain, (![A_1301, B_1302]: (k4_xboole_0(A_1301, B_1302)=k3_subset_1(A_1301, B_1302) | ~m1_subset_1(B_1302, k1_zfmisc_1(A_1301)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 31.98/22.91  tff(c_117475, plain, (![B_1410, A_1411]: (k4_xboole_0(B_1410, A_1411)=k3_subset_1(B_1410, A_1411) | ~r1_tarski(A_1411, B_1410))), inference(resolution, [status(thm)], [c_48, c_114638])).
% 31.98/22.91  tff(c_117556, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_115998, c_117475])).
% 31.98/22.91  tff(c_117701, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_116997, c_117556])).
% 31.98/22.91  tff(c_114494, plain, (![A_1291, B_1292]: (k3_subset_1(A_1291, k3_subset_1(A_1291, B_1292))=B_1292 | ~m1_subset_1(B_1292, k1_zfmisc_1(A_1291)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 31.98/22.91  tff(c_117983, plain, (![B_1415, A_1416]: (k3_subset_1(B_1415, k3_subset_1(B_1415, A_1416))=A_1416 | ~r1_tarski(A_1416, B_1415))), inference(resolution, [status(thm)], [c_48, c_114494])).
% 31.98/22.91  tff(c_118007, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_117701, c_117983])).
% 31.98/22.91  tff(c_118031, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115998, c_118007])).
% 31.98/22.91  tff(c_117070, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116997, c_77])).
% 31.98/22.91  tff(c_30, plain, (![A_29, B_30]: (m1_subset_1(k3_subset_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 31.98/22.91  tff(c_119259, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_118031, c_30])).
% 31.98/22.91  tff(c_119269, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_117070, c_119259])).
% 31.98/22.91  tff(c_129702, plain, (![A_1596, B_1597]: (k4_xboole_0(A_1596, k3_subset_1(A_1596, B_1597))=k3_subset_1(A_1596, k3_subset_1(A_1596, B_1597)) | ~m1_subset_1(B_1597, k1_zfmisc_1(A_1596)))), inference(resolution, [status(thm)], [c_30, c_114638])).
% 31.98/22.91  tff(c_129710, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_119269, c_129702])).
% 31.98/22.91  tff(c_129739, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118031, c_117701, c_117701, c_129710])).
% 31.98/22.91  tff(c_129741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115126, c_129739])).
% 31.98/22.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.98/22.91  
% 31.98/22.91  Inference rules
% 31.98/22.91  ----------------------
% 31.98/22.91  #Ref     : 0
% 31.98/22.91  #Sup     : 30938
% 31.98/22.91  #Fact    : 0
% 31.98/22.91  #Define  : 0
% 31.98/22.91  #Split   : 13
% 31.98/22.91  #Chain   : 0
% 31.98/22.91  #Close   : 0
% 31.98/22.91  
% 31.98/22.91  Ordering : KBO
% 31.98/22.91  
% 31.98/22.91  Simplification rules
% 31.98/22.91  ----------------------
% 31.98/22.91  #Subsume      : 1831
% 31.98/22.91  #Demod        : 32582
% 31.98/22.91  #Tautology    : 19076
% 31.98/22.91  #SimpNegUnit  : 33
% 31.98/22.91  #BackRed      : 69
% 31.98/22.91  
% 31.98/22.91  #Partial instantiations: 0
% 31.98/22.91  #Strategies tried      : 1
% 31.98/22.91  
% 31.98/22.91  Timing (in seconds)
% 31.98/22.91  ----------------------
% 31.98/22.92  Preprocessing        : 0.37
% 31.98/22.92  Parsing              : 0.20
% 31.98/22.92  CNF conversion       : 0.02
% 31.98/22.92  Main loop            : 21.77
% 31.98/22.92  Inferencing          : 2.44
% 31.98/22.92  Reduction            : 13.18
% 31.98/22.92  Demodulation         : 11.77
% 31.98/22.92  BG Simplification    : 0.25
% 31.98/22.92  Subsumption          : 4.82
% 31.98/22.92  Abstraction          : 0.47
% 31.98/22.92  MUC search           : 0.00
% 31.98/22.92  Cooper               : 0.00
% 31.98/22.92  Total                : 22.18
% 31.98/22.92  Index Insertion      : 0.00
% 31.98/22.92  Index Deletion       : 0.00
% 31.98/22.92  Index Matching       : 0.00
% 31.98/22.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
