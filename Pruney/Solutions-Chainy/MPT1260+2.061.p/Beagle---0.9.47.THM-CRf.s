%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:08 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 147 expanded)
%              Number of leaves         :   30 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 348 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_107,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22,plain,(
    ! [C_34,A_22,D_36,B_30] :
      ( v3_pre_topc(C_34,A_22)
      | k1_tops_1(A_22,C_34) != C_34
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0(B_30)))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(B_30)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1032,plain,(
    ! [D_98,B_99] :
      ( ~ m1_subset_1(D_98,k1_zfmisc_1(u1_struct_0(B_99)))
      | ~ l1_pre_topc(B_99) ) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_1035,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1032])).

tff(c_1039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1035])).

tff(c_1042,plain,(
    ! [C_100,A_101] :
      ( v3_pre_topc(C_100,A_101)
      | k1_tops_1(A_101,C_100) != C_100
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1048,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1042])).

tff(c_1052,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1048])).

tff(c_1053,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1052])).

tff(c_243,plain,(
    ! [A_62,B_63,C_64] :
      ( k7_subset_1(A_62,B_63,C_64) = k4_xboole_0(B_63,C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_246,plain,(
    ! [C_64] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_64) = k4_xboole_0('#skF_2',C_64) ),
    inference(resolution,[status(thm)],[c_30,c_243])).

tff(c_782,plain,(
    ! [A_88,B_89] :
      ( k7_subset_1(u1_struct_0(A_88),B_89,k2_tops_1(A_88,B_89)) = k1_tops_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_786,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_782])).

tff(c_790,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_246,c_786])).

tff(c_410,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(B_72,k2_pre_topc(A_73,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_412,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_410])).

tff(c_415,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_412])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_419,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_415,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_561,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k2_pre_topc(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( k7_subset_1(A_9,B_10,C_11) = k4_xboole_0(B_10,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1065,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(u1_struct_0(A_102),k2_pre_topc(A_102,B_103),C_104) = k4_xboole_0(k2_pre_topc(A_102,B_103),C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_561,c_12])).

tff(c_1069,plain,(
    ! [C_104] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_104) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_104)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1065])).

tff(c_1074,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_105) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1069])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_334,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_42])).

tff(c_1084,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_334])).

tff(c_82,plain,(
    ! [A_50,B_51] : r1_xboole_0(k3_xboole_0(A_50,B_51),k4_xboole_0(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_54,A_55] : r1_xboole_0(k3_xboole_0(B_54,A_55),k4_xboole_0(A_55,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [B_58,A_59] : k4_xboole_0(k3_xboole_0(B_58,A_59),k4_xboole_0(A_59,B_58)) = k3_xboole_0(B_58,A_59) ),
    inference(resolution,[status(thm)],[c_94,c_6])).

tff(c_175,plain,(
    ! [A_1,B_2] : k4_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_137])).

tff(c_1121,plain,(
    k4_xboole_0(k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_175])).

tff(c_1143,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_419,c_2,c_419,c_1121])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_1143])).

tff(c_1146,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1147,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_24,plain,(
    ! [B_30,D_36,C_34,A_22] :
      ( k1_tops_1(B_30,D_36) = D_36
      | ~ v3_pre_topc(D_36,B_30)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(u1_struct_0(B_30)))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(B_30)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1934,plain,(
    ! [C_142,A_143] :
      ( ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_1940,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1934])).

tff(c_1945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1940])).

tff(c_1947,plain,(
    ! [B_144,D_145] :
      ( k1_tops_1(B_144,D_145) = D_145
      | ~ v3_pre_topc(D_145,B_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(u1_struct_0(B_144)))
      | ~ l1_pre_topc(B_144) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1953,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1947])).

tff(c_1957,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1147,c_1953])).

tff(c_20,plain,(
    ! [A_19,B_21] :
      ( k7_subset_1(u1_struct_0(A_19),k2_pre_topc(A_19,B_21),k1_tops_1(A_19,B_21)) = k2_tops_1(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1967,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1957,c_20])).

tff(c_1974,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1967])).

tff(c_1976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1146,c_1974])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:23:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.63  
% 3.65/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.63  %$ v3_pre_topc > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.65/1.63  
% 3.65/1.63  %Foreground sorts:
% 3.65/1.63  
% 3.65/1.63  
% 3.65/1.63  %Background operators:
% 3.65/1.63  
% 3.65/1.63  
% 3.65/1.63  %Foreground operators:
% 3.65/1.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.65/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.65/1.63  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.65/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.65/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.63  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.65/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.65/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.63  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.65/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.65/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.65/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.65/1.63  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.65/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.63  
% 3.99/1.65  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 3.99/1.65  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.99/1.65  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.99/1.65  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 3.99/1.65  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.99/1.65  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.99/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.99/1.65  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.99/1.65  tff(f_37, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 3.99/1.65  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.99/1.65  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.99/1.65  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.99/1.65  tff(c_107, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.99/1.65  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.99/1.65  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.99/1.65  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.99/1.65  tff(c_22, plain, (![C_34, A_22, D_36, B_30]: (v3_pre_topc(C_34, A_22) | k1_tops_1(A_22, C_34)!=C_34 | ~m1_subset_1(D_36, k1_zfmisc_1(u1_struct_0(B_30))) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(B_30) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.99/1.65  tff(c_1032, plain, (![D_98, B_99]: (~m1_subset_1(D_98, k1_zfmisc_1(u1_struct_0(B_99))) | ~l1_pre_topc(B_99))), inference(splitLeft, [status(thm)], [c_22])).
% 3.99/1.65  tff(c_1035, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1032])).
% 3.99/1.65  tff(c_1039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1035])).
% 3.99/1.65  tff(c_1042, plain, (![C_100, A_101]: (v3_pre_topc(C_100, A_101) | k1_tops_1(A_101, C_100)!=C_100 | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(splitRight, [status(thm)], [c_22])).
% 3.99/1.65  tff(c_1048, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1042])).
% 3.99/1.65  tff(c_1052, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1048])).
% 3.99/1.65  tff(c_1053, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_107, c_1052])).
% 3.99/1.65  tff(c_243, plain, (![A_62, B_63, C_64]: (k7_subset_1(A_62, B_63, C_64)=k4_xboole_0(B_63, C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.65  tff(c_246, plain, (![C_64]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_64)=k4_xboole_0('#skF_2', C_64))), inference(resolution, [status(thm)], [c_30, c_243])).
% 3.99/1.65  tff(c_782, plain, (![A_88, B_89]: (k7_subset_1(u1_struct_0(A_88), B_89, k2_tops_1(A_88, B_89))=k1_tops_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.99/1.65  tff(c_786, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_782])).
% 3.99/1.65  tff(c_790, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_246, c_786])).
% 3.99/1.65  tff(c_410, plain, (![B_72, A_73]: (r1_tarski(B_72, k2_pre_topc(A_73, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.99/1.65  tff(c_412, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_410])).
% 3.99/1.65  tff(c_415, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_412])).
% 3.99/1.65  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.65  tff(c_419, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_415, c_4])).
% 3.99/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.65  tff(c_561, plain, (![A_76, B_77]: (m1_subset_1(k2_pre_topc(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.99/1.65  tff(c_12, plain, (![A_9, B_10, C_11]: (k7_subset_1(A_9, B_10, C_11)=k4_xboole_0(B_10, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.65  tff(c_1065, plain, (![A_102, B_103, C_104]: (k7_subset_1(u1_struct_0(A_102), k2_pre_topc(A_102, B_103), C_104)=k4_xboole_0(k2_pre_topc(A_102, B_103), C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_561, c_12])).
% 3.99/1.65  tff(c_1069, plain, (![C_104]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_104)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_104) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1065])).
% 3.99/1.65  tff(c_1074, plain, (![C_105]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_105)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_105))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1069])).
% 3.99/1.65  tff(c_42, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.99/1.65  tff(c_334, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_107, c_42])).
% 3.99/1.65  tff(c_1084, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1074, c_334])).
% 3.99/1.65  tff(c_82, plain, (![A_50, B_51]: (r1_xboole_0(k3_xboole_0(A_50, B_51), k4_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.65  tff(c_94, plain, (![B_54, A_55]: (r1_xboole_0(k3_xboole_0(B_54, A_55), k4_xboole_0(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 3.99/1.65  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.99/1.65  tff(c_137, plain, (![B_58, A_59]: (k4_xboole_0(k3_xboole_0(B_58, A_59), k4_xboole_0(A_59, B_58))=k3_xboole_0(B_58, A_59))), inference(resolution, [status(thm)], [c_94, c_6])).
% 3.99/1.65  tff(c_175, plain, (![A_1, B_2]: (k4_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_137])).
% 3.99/1.65  tff(c_1121, plain, (k4_xboole_0(k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1084, c_175])).
% 3.99/1.65  tff(c_1143, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_790, c_419, c_2, c_419, c_1121])).
% 3.99/1.65  tff(c_1145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1053, c_1143])).
% 3.99/1.65  tff(c_1146, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.99/1.65  tff(c_1147, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.99/1.65  tff(c_24, plain, (![B_30, D_36, C_34, A_22]: (k1_tops_1(B_30, D_36)=D_36 | ~v3_pre_topc(D_36, B_30) | ~m1_subset_1(D_36, k1_zfmisc_1(u1_struct_0(B_30))) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(B_30) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.99/1.65  tff(c_1934, plain, (![C_142, A_143]: (~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143))), inference(splitLeft, [status(thm)], [c_24])).
% 3.99/1.65  tff(c_1940, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1934])).
% 3.99/1.65  tff(c_1945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1940])).
% 3.99/1.65  tff(c_1947, plain, (![B_144, D_145]: (k1_tops_1(B_144, D_145)=D_145 | ~v3_pre_topc(D_145, B_144) | ~m1_subset_1(D_145, k1_zfmisc_1(u1_struct_0(B_144))) | ~l1_pre_topc(B_144))), inference(splitRight, [status(thm)], [c_24])).
% 3.99/1.65  tff(c_1953, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1947])).
% 3.99/1.65  tff(c_1957, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1147, c_1953])).
% 3.99/1.65  tff(c_20, plain, (![A_19, B_21]: (k7_subset_1(u1_struct_0(A_19), k2_pre_topc(A_19, B_21), k1_tops_1(A_19, B_21))=k2_tops_1(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.99/1.65  tff(c_1967, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1957, c_20])).
% 3.99/1.65  tff(c_1974, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1967])).
% 3.99/1.65  tff(c_1976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1146, c_1974])).
% 3.99/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.65  
% 3.99/1.65  Inference rules
% 3.99/1.65  ----------------------
% 3.99/1.65  #Ref     : 0
% 3.99/1.65  #Sup     : 483
% 3.99/1.65  #Fact    : 0
% 3.99/1.65  #Define  : 0
% 3.99/1.65  #Split   : 4
% 3.99/1.65  #Chain   : 0
% 3.99/1.65  #Close   : 0
% 3.99/1.65  
% 3.99/1.65  Ordering : KBO
% 3.99/1.65  
% 3.99/1.65  Simplification rules
% 3.99/1.65  ----------------------
% 3.99/1.65  #Subsume      : 41
% 3.99/1.65  #Demod        : 504
% 3.99/1.65  #Tautology    : 191
% 3.99/1.65  #SimpNegUnit  : 4
% 3.99/1.65  #BackRed      : 10
% 3.99/1.65  
% 3.99/1.65  #Partial instantiations: 0
% 3.99/1.65  #Strategies tried      : 1
% 3.99/1.65  
% 3.99/1.65  Timing (in seconds)
% 3.99/1.65  ----------------------
% 3.99/1.65  Preprocessing        : 0.31
% 3.99/1.65  Parsing              : 0.16
% 3.99/1.65  CNF conversion       : 0.02
% 3.99/1.65  Main loop            : 0.58
% 3.99/1.65  Inferencing          : 0.15
% 3.99/1.65  Reduction            : 0.28
% 3.99/1.65  Demodulation         : 0.23
% 3.99/1.65  BG Simplification    : 0.02
% 3.99/1.65  Subsumption          : 0.08
% 3.99/1.65  Abstraction          : 0.03
% 3.99/1.65  MUC search           : 0.00
% 3.99/1.65  Cooper               : 0.00
% 3.99/1.65  Total                : 0.93
% 3.99/1.65  Index Insertion      : 0.00
% 3.99/1.65  Index Deletion       : 0.00
% 3.99/1.65  Index Matching       : 0.00
% 3.99/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
