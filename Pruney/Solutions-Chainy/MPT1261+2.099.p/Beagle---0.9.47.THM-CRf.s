%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 8.29s
% Output     : CNFRefutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 511 expanded)
%              Number of leaves         :   41 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          :  186 ( 779 expanded)
%              Number of equality atoms :   99 ( 351 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_13014,plain,(
    ! [A_369,B_370,C_371] :
      ( k7_subset_1(A_369,B_370,C_371) = k4_xboole_0(B_370,C_371)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(A_369)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13020,plain,(
    ! [C_371] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_371) = k4_xboole_0('#skF_2',C_371) ),
    inference(resolution,[status(thm)],[c_46,c_13014])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_214,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1817,plain,(
    ! [B_132,A_133] :
      ( v4_pre_topc(B_132,A_133)
      | k2_pre_topc(A_133,B_132) != B_132
      | ~ v2_pre_topc(A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1827,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1817])).

tff(c_1832,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_1827])).

tff(c_1833,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1832])).

tff(c_2106,plain,(
    ! [A_141,B_142] :
      ( k4_subset_1(u1_struct_0(A_141),B_142,k2_tops_1(A_141,B_142)) = k2_pre_topc(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2113,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2106])).

tff(c_2118,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2113])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1689,plain,(
    ! [A_126,B_127,C_128] :
      ( k4_subset_1(A_126,B_127,C_128) = k2_xboole_0(B_127,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8161,plain,(
    ! [A_263,B_264,B_265] :
      ( k4_subset_1(u1_struct_0(A_263),B_264,k2_tops_1(A_263,B_265)) = k2_xboole_0(B_264,k2_tops_1(A_263,B_265))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(resolution,[status(thm)],[c_38,c_1689])).

tff(c_8168,plain,(
    ! [B_265] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_265)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_265))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_8161])).

tff(c_8177,plain,(
    ! [B_266] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_266)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_266))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8168])).

tff(c_8188,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_8177])).

tff(c_8194,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_8188])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_773,plain,(
    ! [A_94,B_95,C_96] :
      ( k7_subset_1(A_94,B_95,C_96) = k4_xboole_0(B_95,C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_820,plain,(
    ! [C_99] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_99) = k4_xboole_0('#skF_2',C_99) ),
    inference(resolution,[status(thm)],[c_46,c_773])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_156,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_826,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_156])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_318,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k2_xboole_0(B_70,C_71))
      | ~ r1_tarski(k4_xboole_0(A_69,B_70),C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_336,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(B_73,A_72)) ),
    inference(resolution,[status(thm)],[c_16,c_318])).

tff(c_360,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_336])).

tff(c_71,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_48] : k2_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_195,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_87])).

tff(c_211,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = B_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_202])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_378,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1238,plain,(
    ! [B_112,A_113] :
      ( k4_xboole_0(B_112,A_113) = k3_subset_1(B_112,A_113)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_32,c_378])).

tff(c_1268,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = k3_subset_1(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_360,c_1238])).

tff(c_1292,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1268])).

tff(c_574,plain,(
    ! [A_84,B_85] :
      ( k3_subset_1(A_84,k3_subset_1(A_84,B_85)) = B_85
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1834,plain,(
    ! [B_134,A_135] :
      ( k3_subset_1(B_134,k3_subset_1(B_134,A_135)) = A_135
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(resolution,[status(thm)],[c_32,c_574])).

tff(c_1852,plain,(
    ! [A_7] :
      ( k3_subset_1(A_7,A_7) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_1834])).

tff(c_1867,plain,(
    ! [A_7] : k3_subset_1(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_1852])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1297,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_1238])).

tff(c_169,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_181,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_169])).

tff(c_247,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_259,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_247])).

tff(c_1311,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_259])).

tff(c_1881,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1311])).

tff(c_288,plain,(
    ! [A_65,B_66] : k3_xboole_0(k4_xboole_0(A_65,B_66),A_65) = k4_xboole_0(A_65,B_66) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_294,plain,(
    ! [A_65,B_66] : k5_xboole_0(k4_xboole_0(A_65,B_66),k4_xboole_0(A_65,B_66)) = k4_xboole_0(k4_xboole_0(A_65,B_66),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_10])).

tff(c_11705,plain,(
    ! [A_317,B_318] : k4_xboole_0(k4_xboole_0(A_317,B_318),A_317) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_294])).

tff(c_11843,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_11705])).

tff(c_1312,plain,(
    ! [B_115] : k4_xboole_0(B_115,B_115) = k3_subset_1(B_115,B_115) ),
    inference(resolution,[status(thm)],[c_8,c_1238])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1341,plain,(
    ! [B_115] : k2_xboole_0(B_115,k3_subset_1(B_115,B_115)) = k2_xboole_0(B_115,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_1312,c_18])).

tff(c_1878,plain,(
    ! [B_115] : k2_xboole_0(B_115,k1_xboole_0) = k2_xboole_0(B_115,B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1341])).

tff(c_1886,plain,(
    ! [B_115] : k2_xboole_0(B_115,B_115) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1878])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_534,plain,(
    ! [A_82,B_83] : k3_xboole_0(A_82,k2_xboole_0(B_83,A_82)) = A_82 ),
    inference(resolution,[status(thm)],[c_336,c_14])).

tff(c_544,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(B_83,A_82)) = k5_xboole_0(A_82,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_10])).

tff(c_569,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(B_83,A_82)) = k4_xboole_0(A_82,A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_544])).

tff(c_1620,plain,(
    ! [A_124,B_125] : k4_xboole_0(A_124,k2_xboole_0(B_125,A_124)) = k3_subset_1(A_124,A_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_569])).

tff(c_1673,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k3_subset_1(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1620])).

tff(c_2123,plain,(
    ! [A_143,B_144] : k4_xboole_0(A_143,k2_xboole_0(A_143,B_144)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1673])).

tff(c_2146,plain,(
    ! [A_143,B_144] : k2_xboole_0(k2_xboole_0(A_143,B_144),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_143,B_144),A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_2123,c_18])).

tff(c_3127,plain,(
    ! [A_176,B_177] : k2_xboole_0(k2_xboole_0(A_176,B_177),A_176) = k2_xboole_0(A_176,B_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2146])).

tff(c_2184,plain,(
    ! [A_143,B_144] : k2_xboole_0(k2_xboole_0(A_143,B_144),A_143) = k2_xboole_0(A_143,B_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2146])).

tff(c_3130,plain,(
    ! [A_176,B_177] : k2_xboole_0(k2_xboole_0(A_176,B_177),k2_xboole_0(A_176,B_177)) = k2_xboole_0(k2_xboole_0(A_176,B_177),A_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_3127,c_2184])).

tff(c_3254,plain,(
    ! [A_176,B_177] : k2_xboole_0(A_176,k2_xboole_0(A_176,B_177)) = k2_xboole_0(A_176,B_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1886,c_2,c_3130])).

tff(c_1309,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k2_xboole_0(B_83,A_82)) = k3_subset_1(A_82,A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_569])).

tff(c_2193,plain,(
    ! [A_145,B_146] : k4_xboole_0(A_145,k2_xboole_0(B_146,A_145)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1309])).

tff(c_2219,plain,(
    ! [B_146,A_145] : k2_xboole_0(k2_xboole_0(B_146,A_145),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_146,A_145),A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_18])).

tff(c_3407,plain,(
    ! [B_180,A_181] : k2_xboole_0(k2_xboole_0(B_180,A_181),A_181) = k2_xboole_0(B_180,A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2219])).

tff(c_3629,plain,(
    ! [A_184,B_185] : k2_xboole_0(A_184,k2_xboole_0(B_185,A_184)) = k2_xboole_0(B_185,A_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3407])).

tff(c_5885,plain,(
    ! [B_221,A_222] : k2_xboole_0(B_221,k2_xboole_0(B_221,A_222)) = k2_xboole_0(A_222,B_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3629])).

tff(c_6080,plain,(
    ! [B_13,A_12] : k2_xboole_0(k4_xboole_0(B_13,A_12),A_12) = k2_xboole_0(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5885])).

tff(c_6147,plain,(
    ! [B_13,A_12] : k2_xboole_0(k4_xboole_0(B_13,A_12),A_12) = k2_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_6080])).

tff(c_12341,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11843,c_6147])).

tff(c_12380,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8194,c_12,c_2,c_12341])).

tff(c_12382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1833,c_12380])).

tff(c_12383,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_12474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12383,c_156])).

tff(c_12475,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_12516,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12475,c_52])).

tff(c_13090,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13020,c_12516])).

tff(c_13260,plain,(
    ! [A_382,B_383] :
      ( k2_pre_topc(A_382,B_383) = B_383
      | ~ v4_pre_topc(B_383,A_382)
      | ~ m1_subset_1(B_383,k1_zfmisc_1(u1_struct_0(A_382)))
      | ~ l1_pre_topc(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_13267,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_13260])).

tff(c_13271,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12475,c_13267])).

tff(c_14882,plain,(
    ! [A_438,B_439] :
      ( k7_subset_1(u1_struct_0(A_438),k2_pre_topc(A_438,B_439),k1_tops_1(A_438,B_439)) = k2_tops_1(A_438,B_439)
      | ~ m1_subset_1(B_439,k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ l1_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_14891,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13271,c_14882])).

tff(c_14895,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_13020,c_14891])).

tff(c_14897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13090,c_14895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.29/2.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/3.00  
% 8.29/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/3.01  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.29/3.01  
% 8.29/3.01  %Foreground sorts:
% 8.29/3.01  
% 8.29/3.01  
% 8.29/3.01  %Background operators:
% 8.29/3.01  
% 8.29/3.01  
% 8.29/3.01  %Foreground operators:
% 8.29/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/3.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.29/3.01  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.29/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.29/3.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.29/3.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.29/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.29/3.01  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.29/3.01  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.29/3.01  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.29/3.01  tff('#skF_2', type, '#skF_2': $i).
% 8.29/3.01  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.29/3.01  tff('#skF_1', type, '#skF_1': $i).
% 8.29/3.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.29/3.01  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.29/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/3.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.29/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.29/3.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.29/3.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.29/3.01  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.29/3.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.29/3.01  
% 8.48/3.03  tff(f_126, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.48/3.03  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.48/3.03  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.48/3.03  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.48/3.03  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.48/3.03  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.48/3.03  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.48/3.03  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.48/3.03  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.48/3.03  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.48/3.03  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.48/3.03  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.48/3.03  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.48/3.03  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.48/3.03  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.48/3.03  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.48/3.03  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.48/3.03  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 8.48/3.03  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.48/3.03  tff(c_13014, plain, (![A_369, B_370, C_371]: (k7_subset_1(A_369, B_370, C_371)=k4_xboole_0(B_370, C_371) | ~m1_subset_1(B_370, k1_zfmisc_1(A_369)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.48/3.03  tff(c_13020, plain, (![C_371]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_371)=k4_xboole_0('#skF_2', C_371))), inference(resolution, [status(thm)], [c_46, c_13014])).
% 8.48/3.03  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.48/3.03  tff(c_214, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 8.48/3.03  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.48/3.03  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.48/3.03  tff(c_1817, plain, (![B_132, A_133]: (v4_pre_topc(B_132, A_133) | k2_pre_topc(A_133, B_132)!=B_132 | ~v2_pre_topc(A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.48/3.03  tff(c_1827, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1817])).
% 8.48/3.03  tff(c_1832, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_1827])).
% 8.48/3.03  tff(c_1833, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_214, c_1832])).
% 8.48/3.03  tff(c_2106, plain, (![A_141, B_142]: (k4_subset_1(u1_struct_0(A_141), B_142, k2_tops_1(A_141, B_142))=k2_pre_topc(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.48/3.03  tff(c_2113, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2106])).
% 8.48/3.03  tff(c_2118, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2113])).
% 8.48/3.03  tff(c_38, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.48/3.03  tff(c_1689, plain, (![A_126, B_127, C_128]: (k4_subset_1(A_126, B_127, C_128)=k2_xboole_0(B_127, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.48/3.03  tff(c_8161, plain, (![A_263, B_264, B_265]: (k4_subset_1(u1_struct_0(A_263), B_264, k2_tops_1(A_263, B_265))=k2_xboole_0(B_264, k2_tops_1(A_263, B_265)) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(resolution, [status(thm)], [c_38, c_1689])).
% 8.48/3.03  tff(c_8168, plain, (![B_265]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_265))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_265)) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_8161])).
% 8.48/3.03  tff(c_8177, plain, (![B_266]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_266))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_266)) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8168])).
% 8.48/3.03  tff(c_8188, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_8177])).
% 8.48/3.03  tff(c_8194, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_8188])).
% 8.48/3.03  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.48/3.03  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.48/3.03  tff(c_773, plain, (![A_94, B_95, C_96]: (k7_subset_1(A_94, B_95, C_96)=k4_xboole_0(B_95, C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.48/3.03  tff(c_820, plain, (![C_99]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_99)=k4_xboole_0('#skF_2', C_99))), inference(resolution, [status(thm)], [c_46, c_773])).
% 8.48/3.03  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.48/3.03  tff(c_156, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 8.48/3.03  tff(c_826, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_820, c_156])).
% 8.48/3.03  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.48/3.03  tff(c_318, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k2_xboole_0(B_70, C_71)) | ~r1_tarski(k4_xboole_0(A_69, B_70), C_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.48/3.03  tff(c_336, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(B_73, A_72)))), inference(resolution, [status(thm)], [c_16, c_318])).
% 8.48/3.03  tff(c_360, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_336])).
% 8.48/3.03  tff(c_71, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.48/3.03  tff(c_87, plain, (![A_48]: (k2_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_71, c_12])).
% 8.48/3.03  tff(c_195, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.48/3.03  tff(c_202, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_195, c_87])).
% 8.48/3.03  tff(c_211, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_202])).
% 8.48/3.03  tff(c_32, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.48/3.03  tff(c_378, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.48/3.03  tff(c_1238, plain, (![B_112, A_113]: (k4_xboole_0(B_112, A_113)=k3_subset_1(B_112, A_113) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_32, c_378])).
% 8.48/3.03  tff(c_1268, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=k3_subset_1(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_360, c_1238])).
% 8.48/3.03  tff(c_1292, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1268])).
% 8.48/3.03  tff(c_574, plain, (![A_84, B_85]: (k3_subset_1(A_84, k3_subset_1(A_84, B_85))=B_85 | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.48/3.03  tff(c_1834, plain, (![B_134, A_135]: (k3_subset_1(B_134, k3_subset_1(B_134, A_135))=A_135 | ~r1_tarski(A_135, B_134))), inference(resolution, [status(thm)], [c_32, c_574])).
% 8.48/3.03  tff(c_1852, plain, (![A_7]: (k3_subset_1(A_7, A_7)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_1834])).
% 8.48/3.03  tff(c_1867, plain, (![A_7]: (k3_subset_1(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_360, c_1852])).
% 8.48/3.03  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.48/3.03  tff(c_1297, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(resolution, [status(thm)], [c_8, c_1238])).
% 8.48/3.03  tff(c_169, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.48/3.03  tff(c_181, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_169])).
% 8.48/3.03  tff(c_247, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.48/3.03  tff(c_259, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_181, c_247])).
% 8.48/3.03  tff(c_1311, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_259])).
% 8.48/3.03  tff(c_1881, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1311])).
% 8.48/3.03  tff(c_288, plain, (![A_65, B_66]: (k3_xboole_0(k4_xboole_0(A_65, B_66), A_65)=k4_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_16, c_169])).
% 8.48/3.03  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.48/3.03  tff(c_294, plain, (![A_65, B_66]: (k5_xboole_0(k4_xboole_0(A_65, B_66), k4_xboole_0(A_65, B_66))=k4_xboole_0(k4_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_288, c_10])).
% 8.48/3.03  tff(c_11705, plain, (![A_317, B_318]: (k4_xboole_0(k4_xboole_0(A_317, B_318), A_317)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_294])).
% 8.48/3.03  tff(c_11843, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_826, c_11705])).
% 8.48/3.03  tff(c_1312, plain, (![B_115]: (k4_xboole_0(B_115, B_115)=k3_subset_1(B_115, B_115))), inference(resolution, [status(thm)], [c_8, c_1238])).
% 8.48/3.03  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.48/3.03  tff(c_1341, plain, (![B_115]: (k2_xboole_0(B_115, k3_subset_1(B_115, B_115))=k2_xboole_0(B_115, B_115))), inference(superposition, [status(thm), theory('equality')], [c_1312, c_18])).
% 8.48/3.03  tff(c_1878, plain, (![B_115]: (k2_xboole_0(B_115, k1_xboole_0)=k2_xboole_0(B_115, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1341])).
% 8.48/3.03  tff(c_1886, plain, (![B_115]: (k2_xboole_0(B_115, B_115)=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1878])).
% 8.48/3.03  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.48/3.03  tff(c_534, plain, (![A_82, B_83]: (k3_xboole_0(A_82, k2_xboole_0(B_83, A_82))=A_82)), inference(resolution, [status(thm)], [c_336, c_14])).
% 8.48/3.03  tff(c_544, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(B_83, A_82))=k5_xboole_0(A_82, A_82))), inference(superposition, [status(thm), theory('equality')], [c_534, c_10])).
% 8.48/3.03  tff(c_569, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(B_83, A_82))=k4_xboole_0(A_82, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_544])).
% 8.48/3.03  tff(c_1620, plain, (![A_124, B_125]: (k4_xboole_0(A_124, k2_xboole_0(B_125, A_124))=k3_subset_1(A_124, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_569])).
% 8.48/3.03  tff(c_1673, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k3_subset_1(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1620])).
% 8.48/3.03  tff(c_2123, plain, (![A_143, B_144]: (k4_xboole_0(A_143, k2_xboole_0(A_143, B_144))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1673])).
% 8.48/3.03  tff(c_2146, plain, (![A_143, B_144]: (k2_xboole_0(k2_xboole_0(A_143, B_144), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_143, B_144), A_143))), inference(superposition, [status(thm), theory('equality')], [c_2123, c_18])).
% 8.48/3.03  tff(c_3127, plain, (![A_176, B_177]: (k2_xboole_0(k2_xboole_0(A_176, B_177), A_176)=k2_xboole_0(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2146])).
% 8.48/3.03  tff(c_2184, plain, (![A_143, B_144]: (k2_xboole_0(k2_xboole_0(A_143, B_144), A_143)=k2_xboole_0(A_143, B_144))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2146])).
% 8.48/3.03  tff(c_3130, plain, (![A_176, B_177]: (k2_xboole_0(k2_xboole_0(A_176, B_177), k2_xboole_0(A_176, B_177))=k2_xboole_0(k2_xboole_0(A_176, B_177), A_176))), inference(superposition, [status(thm), theory('equality')], [c_3127, c_2184])).
% 8.48/3.03  tff(c_3254, plain, (![A_176, B_177]: (k2_xboole_0(A_176, k2_xboole_0(A_176, B_177))=k2_xboole_0(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_1886, c_2, c_3130])).
% 8.48/3.03  tff(c_1309, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k2_xboole_0(B_83, A_82))=k3_subset_1(A_82, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_569])).
% 8.48/3.03  tff(c_2193, plain, (![A_145, B_146]: (k4_xboole_0(A_145, k2_xboole_0(B_146, A_145))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1309])).
% 8.48/3.03  tff(c_2219, plain, (![B_146, A_145]: (k2_xboole_0(k2_xboole_0(B_146, A_145), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_146, A_145), A_145))), inference(superposition, [status(thm), theory('equality')], [c_2193, c_18])).
% 8.48/3.03  tff(c_3407, plain, (![B_180, A_181]: (k2_xboole_0(k2_xboole_0(B_180, A_181), A_181)=k2_xboole_0(B_180, A_181))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2219])).
% 8.48/3.03  tff(c_3629, plain, (![A_184, B_185]: (k2_xboole_0(A_184, k2_xboole_0(B_185, A_184))=k2_xboole_0(B_185, A_184))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3407])).
% 8.48/3.03  tff(c_5885, plain, (![B_221, A_222]: (k2_xboole_0(B_221, k2_xboole_0(B_221, A_222))=k2_xboole_0(A_222, B_221))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3629])).
% 8.48/3.03  tff(c_6080, plain, (![B_13, A_12]: (k2_xboole_0(k4_xboole_0(B_13, A_12), A_12)=k2_xboole_0(A_12, k2_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5885])).
% 8.48/3.03  tff(c_6147, plain, (![B_13, A_12]: (k2_xboole_0(k4_xboole_0(B_13, A_12), A_12)=k2_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_6080])).
% 8.48/3.03  tff(c_12341, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11843, c_6147])).
% 8.48/3.03  tff(c_12380, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8194, c_12, c_2, c_12341])).
% 8.48/3.03  tff(c_12382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1833, c_12380])).
% 8.48/3.03  tff(c_12383, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 8.48/3.03  tff(c_12474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12383, c_156])).
% 8.48/3.03  tff(c_12475, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 8.48/3.03  tff(c_12516, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12475, c_52])).
% 8.48/3.03  tff(c_13090, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13020, c_12516])).
% 8.48/3.03  tff(c_13260, plain, (![A_382, B_383]: (k2_pre_topc(A_382, B_383)=B_383 | ~v4_pre_topc(B_383, A_382) | ~m1_subset_1(B_383, k1_zfmisc_1(u1_struct_0(A_382))) | ~l1_pre_topc(A_382))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.48/3.03  tff(c_13267, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_13260])).
% 8.48/3.03  tff(c_13271, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12475, c_13267])).
% 8.48/3.03  tff(c_14882, plain, (![A_438, B_439]: (k7_subset_1(u1_struct_0(A_438), k2_pre_topc(A_438, B_439), k1_tops_1(A_438, B_439))=k2_tops_1(A_438, B_439) | ~m1_subset_1(B_439, k1_zfmisc_1(u1_struct_0(A_438))) | ~l1_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.48/3.03  tff(c_14891, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13271, c_14882])).
% 8.48/3.03  tff(c_14895, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_13020, c_14891])).
% 8.48/3.03  tff(c_14897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13090, c_14895])).
% 8.48/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.48/3.03  
% 8.48/3.03  Inference rules
% 8.48/3.03  ----------------------
% 8.48/3.03  #Ref     : 0
% 8.48/3.03  #Sup     : 3574
% 8.48/3.03  #Fact    : 0
% 8.48/3.03  #Define  : 0
% 8.48/3.03  #Split   : 7
% 8.48/3.03  #Chain   : 0
% 8.48/3.03  #Close   : 0
% 8.48/3.03  
% 8.48/3.03  Ordering : KBO
% 8.48/3.03  
% 8.48/3.03  Simplification rules
% 8.48/3.03  ----------------------
% 8.48/3.03  #Subsume      : 101
% 8.48/3.03  #Demod        : 3524
% 8.48/3.03  #Tautology    : 2485
% 8.48/3.03  #SimpNegUnit  : 11
% 8.48/3.03  #BackRed      : 36
% 8.48/3.03  
% 8.48/3.03  #Partial instantiations: 0
% 8.48/3.03  #Strategies tried      : 1
% 8.48/3.03  
% 8.48/3.03  Timing (in seconds)
% 8.48/3.03  ----------------------
% 8.48/3.03  Preprocessing        : 0.34
% 8.48/3.03  Parsing              : 0.18
% 8.48/3.03  CNF conversion       : 0.02
% 8.48/3.03  Main loop            : 1.91
% 8.48/3.03  Inferencing          : 0.47
% 8.48/3.03  Reduction            : 0.96
% 8.48/3.03  Demodulation         : 0.80
% 8.48/3.03  BG Simplification    : 0.05
% 8.48/3.03  Subsumption          : 0.30
% 8.48/3.03  Abstraction          : 0.09
% 8.48/3.03  MUC search           : 0.00
% 8.48/3.03  Cooper               : 0.00
% 8.48/3.03  Total                : 2.29
% 8.48/3.03  Index Insertion      : 0.00
% 8.48/3.03  Index Deletion       : 0.00
% 8.48/3.03  Index Matching       : 0.00
% 8.48/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
