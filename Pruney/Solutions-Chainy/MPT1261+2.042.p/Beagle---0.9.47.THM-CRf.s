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
% DateTime   : Thu Dec  3 10:21:17 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 162 expanded)
%              Number of leaves         :   44 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 292 expanded)
%              Number of equality atoms :   51 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_126,negated_conjecture,(
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

tff(f_86,axiom,(
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

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2509,plain,(
    ! [A_307,B_308,C_309] :
      ( k7_subset_1(A_307,B_308,C_309) = k4_xboole_0(B_308,C_309)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2520,plain,(
    ! [C_309] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_309) = k4_xboole_0('#skF_2',C_309) ),
    inference(resolution,[status(thm)],[c_50,c_2509])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_132,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_240,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1095,plain,(
    ! [B_173,A_174] :
      ( v4_pre_topc(B_173,A_174)
      | k2_pre_topc(A_174,B_173) != B_173
      | ~ v2_pre_topc(A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1125,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1095])).

tff(c_1148,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_1125])).

tff(c_1149,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_1148])).

tff(c_1318,plain,(
    ! [A_193,B_194] :
      ( k4_subset_1(u1_struct_0(A_193),B_194,k2_tops_1(A_193,B_194)) = k2_pre_topc(A_193,B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1339,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1318])).

tff(c_1361,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1339])).

tff(c_364,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(A_102,B_103,C_104) = k4_xboole_0(B_103,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_437,plain,(
    ! [C_116] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_116) = k4_xboole_0('#skF_2',C_116) ),
    inference(resolution,[status(thm)],[c_50,c_364])).

tff(c_452,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_437])).

tff(c_22,plain,(
    ! [A_36] : k2_subset_1(A_36) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_37] : m1_subset_1(k2_subset_1(A_37),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [A_37] : m1_subset_1(A_37,k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_373,plain,(
    ! [A_37,C_104] : k7_subset_1(A_37,A_37,C_104) = k4_xboole_0(A_37,C_104) ),
    inference(resolution,[status(thm)],[c_63,c_364])).

tff(c_383,plain,(
    ! [A_107,B_108,C_109] :
      ( m1_subset_1(k7_subset_1(A_107,B_108,C_109),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_391,plain,(
    ! [A_37,C_104] :
      ( m1_subset_1(k4_xboole_0(A_37,C_104),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_383])).

tff(c_401,plain,(
    ! [A_110,C_111] : m1_subset_1(k4_xboole_0(A_110,C_111),k1_zfmisc_1(A_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_391])).

tff(c_34,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_409,plain,(
    ! [A_112,C_113] : r1_tarski(k4_xboole_0(A_112,C_113),A_112) ),
    inference(resolution,[status(thm)],[c_401,c_34])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_414,plain,(
    ! [A_114,C_115] : k2_xboole_0(k4_xboole_0(A_114,C_115),A_114) = A_114 ),
    inference(resolution,[status(thm)],[c_409,c_4])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_241,plain,(
    ! [A_87,B_88] : k3_tarski(k2_tarski(A_87,B_88)) = k2_xboole_0(B_88,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_20,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_247,plain,(
    ! [B_88,A_87] : k2_xboole_0(B_88,A_87) = k2_xboole_0(A_87,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_20])).

tff(c_420,plain,(
    ! [A_114,C_115] : k2_xboole_0(A_114,k4_xboole_0(A_114,C_115)) = A_114 ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_247])).

tff(c_509,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_420])).

tff(c_394,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_383])).

tff(c_400,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_394])).

tff(c_475,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_400,c_34])).

tff(c_36,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_903,plain,(
    ! [A_162,B_163,C_164] :
      ( k4_subset_1(A_162,B_163,C_164) = k2_xboole_0(B_163,C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1996,plain,(
    ! [B_255,B_256,A_257] :
      ( k4_subset_1(B_255,B_256,A_257) = k2_xboole_0(B_256,A_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(B_255))
      | ~ r1_tarski(A_257,B_255) ) ),
    inference(resolution,[status(thm)],[c_36,c_903])).

tff(c_2099,plain,(
    ! [A_262] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_262) = k2_xboole_0('#skF_2',A_262)
      | ~ r1_tarski(A_262,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1996])).

tff(c_2123,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_475,c_2099])).

tff(c_2147,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_509,c_2123])).

tff(c_2149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1149,c_2147])).

tff(c_2150,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2150])).

tff(c_2268,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2303,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_56])).

tff(c_2522,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2520,c_2303])).

tff(c_2730,plain,(
    ! [A_342,B_343] :
      ( k2_pre_topc(A_342,B_343) = B_343
      | ~ v4_pre_topc(B_343,A_342)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2751,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2730])).

tff(c_2767,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2268,c_2751])).

tff(c_3814,plain,(
    ! [A_471,B_472] :
      ( k7_subset_1(u1_struct_0(A_471),k2_pre_topc(A_471,B_472),k1_tops_1(A_471,B_472)) = k2_tops_1(A_471,B_472)
      | ~ m1_subset_1(B_472,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3835,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2767,c_3814])).

tff(c_3839,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2520,c_3835])).

tff(c_3841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2522,c_3839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:54:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.09  
% 5.61/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.09  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.61/2.09  
% 5.61/2.09  %Foreground sorts:
% 5.61/2.09  
% 5.61/2.09  
% 5.61/2.09  %Background operators:
% 5.61/2.09  
% 5.61/2.09  
% 5.61/2.09  %Foreground operators:
% 5.61/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.61/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.61/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.61/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.61/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.61/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.61/2.09  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.61/2.09  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.61/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.61/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.61/2.09  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.61/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.61/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.61/2.09  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.61/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.61/2.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.61/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.61/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.61/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.61/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.61/2.09  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.61/2.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.61/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.61/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.61/2.09  
% 5.61/2.11  tff(f_126, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.61/2.11  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.61/2.11  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.61/2.11  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.61/2.11  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.61/2.11  tff(f_51, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.61/2.11  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 5.61/2.11  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.61/2.11  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.61/2.11  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.61/2.11  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.61/2.11  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.61/2.11  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.61/2.11  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.61/2.11  tff(c_2509, plain, (![A_307, B_308, C_309]: (k7_subset_1(A_307, B_308, C_309)=k4_xboole_0(B_308, C_309) | ~m1_subset_1(B_308, k1_zfmisc_1(A_307)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.61/2.11  tff(c_2520, plain, (![C_309]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_309)=k4_xboole_0('#skF_2', C_309))), inference(resolution, [status(thm)], [c_50, c_2509])).
% 5.61/2.11  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.61/2.11  tff(c_132, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 5.61/2.11  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.61/2.11  tff(c_240, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 5.61/2.11  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.61/2.11  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.61/2.11  tff(c_1095, plain, (![B_173, A_174]: (v4_pre_topc(B_173, A_174) | k2_pre_topc(A_174, B_173)!=B_173 | ~v2_pre_topc(A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.61/2.11  tff(c_1125, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1095])).
% 5.61/2.11  tff(c_1148, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_1125])).
% 5.61/2.11  tff(c_1149, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_240, c_1148])).
% 5.61/2.11  tff(c_1318, plain, (![A_193, B_194]: (k4_subset_1(u1_struct_0(A_193), B_194, k2_tops_1(A_193, B_194))=k2_pre_topc(A_193, B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.61/2.11  tff(c_1339, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1318])).
% 5.61/2.11  tff(c_1361, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1339])).
% 5.61/2.11  tff(c_364, plain, (![A_102, B_103, C_104]: (k7_subset_1(A_102, B_103, C_104)=k4_xboole_0(B_103, C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.61/2.11  tff(c_437, plain, (![C_116]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_116)=k4_xboole_0('#skF_2', C_116))), inference(resolution, [status(thm)], [c_50, c_364])).
% 5.61/2.11  tff(c_452, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_132, c_437])).
% 5.61/2.11  tff(c_22, plain, (![A_36]: (k2_subset_1(A_36)=A_36)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.61/2.11  tff(c_24, plain, (![A_37]: (m1_subset_1(k2_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.61/2.11  tff(c_63, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 5.61/2.11  tff(c_373, plain, (![A_37, C_104]: (k7_subset_1(A_37, A_37, C_104)=k4_xboole_0(A_37, C_104))), inference(resolution, [status(thm)], [c_63, c_364])).
% 5.61/2.11  tff(c_383, plain, (![A_107, B_108, C_109]: (m1_subset_1(k7_subset_1(A_107, B_108, C_109), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.61/2.11  tff(c_391, plain, (![A_37, C_104]: (m1_subset_1(k4_xboole_0(A_37, C_104), k1_zfmisc_1(A_37)) | ~m1_subset_1(A_37, k1_zfmisc_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_373, c_383])).
% 5.61/2.11  tff(c_401, plain, (![A_110, C_111]: (m1_subset_1(k4_xboole_0(A_110, C_111), k1_zfmisc_1(A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_391])).
% 5.61/2.11  tff(c_34, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.61/2.11  tff(c_409, plain, (![A_112, C_113]: (r1_tarski(k4_xboole_0(A_112, C_113), A_112))), inference(resolution, [status(thm)], [c_401, c_34])).
% 5.61/2.11  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.61/2.11  tff(c_414, plain, (![A_114, C_115]: (k2_xboole_0(k4_xboole_0(A_114, C_115), A_114)=A_114)), inference(resolution, [status(thm)], [c_409, c_4])).
% 5.61/2.11  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.61/2.11  tff(c_165, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.61/2.11  tff(c_241, plain, (![A_87, B_88]: (k3_tarski(k2_tarski(A_87, B_88))=k2_xboole_0(B_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_6, c_165])).
% 5.61/2.11  tff(c_20, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.61/2.11  tff(c_247, plain, (![B_88, A_87]: (k2_xboole_0(B_88, A_87)=k2_xboole_0(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_241, c_20])).
% 5.61/2.11  tff(c_420, plain, (![A_114, C_115]: (k2_xboole_0(A_114, k4_xboole_0(A_114, C_115))=A_114)), inference(superposition, [status(thm), theory('equality')], [c_414, c_247])).
% 5.61/2.11  tff(c_509, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_452, c_420])).
% 5.61/2.11  tff(c_394, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_383])).
% 5.61/2.11  tff(c_400, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_394])).
% 5.61/2.11  tff(c_475, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_400, c_34])).
% 5.61/2.11  tff(c_36, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.61/2.11  tff(c_903, plain, (![A_162, B_163, C_164]: (k4_subset_1(A_162, B_163, C_164)=k2_xboole_0(B_163, C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | ~m1_subset_1(B_163, k1_zfmisc_1(A_162)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.61/2.11  tff(c_1996, plain, (![B_255, B_256, A_257]: (k4_subset_1(B_255, B_256, A_257)=k2_xboole_0(B_256, A_257) | ~m1_subset_1(B_256, k1_zfmisc_1(B_255)) | ~r1_tarski(A_257, B_255))), inference(resolution, [status(thm)], [c_36, c_903])).
% 5.61/2.11  tff(c_2099, plain, (![A_262]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_262)=k2_xboole_0('#skF_2', A_262) | ~r1_tarski(A_262, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_1996])).
% 5.61/2.11  tff(c_2123, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_475, c_2099])).
% 5.61/2.11  tff(c_2147, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_509, c_2123])).
% 5.61/2.11  tff(c_2149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1149, c_2147])).
% 5.61/2.11  tff(c_2150, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 5.61/2.11  tff(c_2267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_2150])).
% 5.61/2.11  tff(c_2268, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 5.61/2.11  tff(c_2303, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2268, c_56])).
% 5.61/2.11  tff(c_2522, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2520, c_2303])).
% 5.61/2.11  tff(c_2730, plain, (![A_342, B_343]: (k2_pre_topc(A_342, B_343)=B_343 | ~v4_pre_topc(B_343, A_342) | ~m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0(A_342))) | ~l1_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.61/2.11  tff(c_2751, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2730])).
% 5.61/2.11  tff(c_2767, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2268, c_2751])).
% 5.61/2.11  tff(c_3814, plain, (![A_471, B_472]: (k7_subset_1(u1_struct_0(A_471), k2_pre_topc(A_471, B_472), k1_tops_1(A_471, B_472))=k2_tops_1(A_471, B_472) | ~m1_subset_1(B_472, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.61/2.11  tff(c_3835, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2767, c_3814])).
% 5.61/2.11  tff(c_3839, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2520, c_3835])).
% 5.61/2.11  tff(c_3841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2522, c_3839])).
% 5.61/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.11  
% 5.61/2.11  Inference rules
% 5.61/2.11  ----------------------
% 5.61/2.11  #Ref     : 0
% 5.61/2.11  #Sup     : 886
% 5.61/2.11  #Fact    : 0
% 5.61/2.11  #Define  : 0
% 5.61/2.11  #Split   : 3
% 5.61/2.11  #Chain   : 0
% 5.61/2.11  #Close   : 0
% 5.61/2.11  
% 5.61/2.11  Ordering : KBO
% 5.61/2.11  
% 5.61/2.11  Simplification rules
% 5.61/2.11  ----------------------
% 5.61/2.11  #Subsume      : 18
% 5.61/2.11  #Demod        : 505
% 5.61/2.11  #Tautology    : 512
% 5.61/2.11  #SimpNegUnit  : 4
% 5.61/2.11  #BackRed      : 5
% 5.61/2.11  
% 5.61/2.11  #Partial instantiations: 0
% 5.61/2.11  #Strategies tried      : 1
% 5.61/2.11  
% 5.61/2.11  Timing (in seconds)
% 5.61/2.11  ----------------------
% 5.61/2.11  Preprocessing        : 0.35
% 5.61/2.11  Parsing              : 0.19
% 5.61/2.11  CNF conversion       : 0.02
% 5.61/2.11  Main loop            : 0.99
% 5.61/2.11  Inferencing          : 0.34
% 5.61/2.11  Reduction            : 0.38
% 5.61/2.11  Demodulation         : 0.29
% 5.61/2.11  BG Simplification    : 0.04
% 5.61/2.11  Subsumption          : 0.16
% 5.61/2.11  Abstraction          : 0.05
% 5.61/2.11  MUC search           : 0.00
% 5.61/2.11  Cooper               : 0.00
% 5.61/2.11  Total                : 1.38
% 5.61/2.11  Index Insertion      : 0.00
% 5.61/2.11  Index Deletion       : 0.00
% 5.61/2.11  Index Matching       : 0.00
% 5.61/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
