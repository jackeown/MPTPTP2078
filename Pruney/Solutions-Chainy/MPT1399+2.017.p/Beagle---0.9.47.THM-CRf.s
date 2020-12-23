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
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 246 expanded)
%              Number of leaves         :   36 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 742 expanded)
%              Number of equality atoms :   13 (  98 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    ! [A_21] :
      ( v4_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_120,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_42,c_120])).

tff(c_129,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_131,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_54])).

tff(c_137,plain,(
    ! [B_47,A_48] :
      ( v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_146,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_131,c_137])).

tff(c_147,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_22] :
      ( v3_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_187,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(B_61,A_62)
      | ~ r2_hidden(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_194,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_187])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_26])).

tff(c_102,plain,(
    ! [A_41,B_42] : ~ r2_hidden(A_41,k2_zfmisc_1(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,(
    ! [A_12] : ~ r2_hidden(A_12,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_102])).

tff(c_62,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_6')
      | ~ r2_hidden('#skF_5',D_34)
      | ~ v4_pre_topc(D_34,'#skF_4')
      | ~ v3_pre_topc(D_34,'#skF_4')
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_299,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_6')
      | ~ r2_hidden('#skF_5',D_34)
      | ~ v4_pre_topc(D_34,'#skF_4')
      | ~ v3_pre_topc(D_34,'#skF_4')
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_62])).

tff(c_301,plain,(
    ! [D_79] :
      ( ~ r2_hidden('#skF_5',D_79)
      | ~ v4_pre_topc(D_79,'#skF_4')
      | ~ v3_pre_topc(D_79,'#skF_4')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_299])).

tff(c_314,plain,(
    ! [C_11] :
      ( ~ r2_hidden('#skF_5',C_11)
      | ~ v4_pre_topc(C_11,'#skF_4')
      | ~ v3_pre_topc(C_11,'#skF_4')
      | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r1_tarski(C_11,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_194,c_301])).

tff(c_380,plain,(
    ! [C_93] :
      ( ~ r2_hidden('#skF_5',C_93)
      | ~ v4_pre_topc(C_93,'#skF_4')
      | ~ v3_pre_topc(C_93,'#skF_4')
      | ~ r1_tarski(C_93,k2_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_405,plain,
    ( ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_380])).

tff(c_406,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_409,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_406])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_409])).

tff(c_414,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_439,plain,(
    ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_442,plain,
    ( ~ m1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_439])).

tff(c_445,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_445])).

tff(c_448,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_463,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_448])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_463])).

tff(c_468,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_164,plain,(
    ! [C_54,A_55] :
      ( r2_hidden(C_54,k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_54,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_55,C_54] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_54,A_55) ) ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_472,plain,(
    ! [C_96] : ~ r1_tarski(C_96,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_468,c_172])).

tff(c_498,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_472])).

tff(c_500,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_512,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(u1_struct_0(A_101))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_515,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_512])).

tff(c_517,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_515])).

tff(c_518,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_517])).

tff(c_521,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_518])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.39  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.73/1.39  
% 2.73/1.39  %Foreground sorts:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Background operators:
% 2.73/1.39  
% 2.73/1.39  
% 2.73/1.39  %Foreground operators:
% 2.73/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.73/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.73/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.73/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.73/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.39  
% 2.73/1.40  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.73/1.40  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.73/1.40  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.40  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.73/1.40  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.73/1.40  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.73/1.40  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.73/1.40  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.73/1.40  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.40  tff(f_53, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.73/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.73/1.40  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.73/1.40  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.73/1.40  tff(c_42, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.40  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.73/1.40  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.40  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.73/1.40  tff(c_46, plain, (![A_21]: (v4_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.40  tff(c_120, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.73/1.40  tff(c_125, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_42, c_120])).
% 2.73/1.40  tff(c_129, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_125])).
% 2.73/1.40  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.73/1.40  tff(c_131, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_54])).
% 2.73/1.40  tff(c_137, plain, (![B_47, A_48]: (v1_xboole_0(B_47) | ~m1_subset_1(B_47, A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.40  tff(c_146, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_131, c_137])).
% 2.73/1.40  tff(c_147, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_146])).
% 2.73/1.40  tff(c_34, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.40  tff(c_48, plain, (![A_22]: (v3_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.73/1.40  tff(c_14, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.40  tff(c_187, plain, (![B_61, A_62]: (m1_subset_1(B_61, A_62) | ~r2_hidden(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.40  tff(c_194, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(resolution, [status(thm)], [c_14, c_187])).
% 2.73/1.40  tff(c_50, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.73/1.40  tff(c_26, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.73/1.40  tff(c_70, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_26])).
% 2.73/1.40  tff(c_102, plain, (![A_41, B_42]: (~r2_hidden(A_41, k2_zfmisc_1(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.40  tff(c_108, plain, (![A_12]: (~r2_hidden(A_12, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_102])).
% 2.73/1.40  tff(c_62, plain, (![D_34]: (r2_hidden(D_34, '#skF_6') | ~r2_hidden('#skF_5', D_34) | ~v4_pre_topc(D_34, '#skF_4') | ~v3_pre_topc(D_34, '#skF_4') | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.73/1.40  tff(c_299, plain, (![D_34]: (r2_hidden(D_34, '#skF_6') | ~r2_hidden('#skF_5', D_34) | ~v4_pre_topc(D_34, '#skF_4') | ~v3_pre_topc(D_34, '#skF_4') | ~m1_subset_1(D_34, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_62])).
% 2.73/1.40  tff(c_301, plain, (![D_79]: (~r2_hidden('#skF_5', D_79) | ~v4_pre_topc(D_79, '#skF_4') | ~v3_pre_topc(D_79, '#skF_4') | ~m1_subset_1(D_79, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_108, c_299])).
% 2.73/1.40  tff(c_314, plain, (![C_11]: (~r2_hidden('#skF_5', C_11) | ~v4_pre_topc(C_11, '#skF_4') | ~v3_pre_topc(C_11, '#skF_4') | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~r1_tarski(C_11, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_194, c_301])).
% 2.73/1.40  tff(c_380, plain, (![C_93]: (~r2_hidden('#skF_5', C_93) | ~v4_pre_topc(C_93, '#skF_4') | ~v3_pre_topc(C_93, '#skF_4') | ~r1_tarski(C_93, k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_314])).
% 2.73/1.40  tff(c_405, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_10, c_380])).
% 2.73/1.40  tff(c_406, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_405])).
% 2.73/1.40  tff(c_409, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_406])).
% 2.73/1.40  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_409])).
% 2.73/1.40  tff(c_414, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_405])).
% 2.73/1.40  tff(c_439, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_414])).
% 2.73/1.40  tff(c_442, plain, (~m1_subset_1('#skF_5', k2_struct_0('#skF_4')) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_439])).
% 2.73/1.40  tff(c_445, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_442])).
% 2.73/1.40  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_445])).
% 2.73/1.40  tff(c_448, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_414])).
% 2.73/1.40  tff(c_463, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_448])).
% 2.73/1.40  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_463])).
% 2.73/1.40  tff(c_468, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_314])).
% 2.73/1.40  tff(c_164, plain, (![C_54, A_55]: (r2_hidden(C_54, k1_zfmisc_1(A_55)) | ~r1_tarski(C_54, A_55))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.40  tff(c_172, plain, (![A_55, C_54]: (~v1_xboole_0(k1_zfmisc_1(A_55)) | ~r1_tarski(C_54, A_55))), inference(resolution, [status(thm)], [c_164, c_2])).
% 2.73/1.40  tff(c_472, plain, (![C_96]: (~r1_tarski(C_96, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_468, c_172])).
% 2.73/1.40  tff(c_498, plain, $false, inference(resolution, [status(thm)], [c_10, c_472])).
% 2.73/1.40  tff(c_500, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_146])).
% 2.73/1.40  tff(c_512, plain, (![A_101]: (~v1_xboole_0(u1_struct_0(A_101)) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.40  tff(c_515, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_512])).
% 2.73/1.40  tff(c_517, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_515])).
% 2.73/1.40  tff(c_518, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_517])).
% 2.73/1.40  tff(c_521, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_518])).
% 2.73/1.40  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_521])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 88
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 7
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 12
% 2.73/1.40  #Demod        : 31
% 2.73/1.40  #Tautology    : 31
% 2.73/1.40  #SimpNegUnit  : 5
% 2.73/1.40  #BackRed      : 2
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.33
% 2.73/1.40  Parsing              : 0.17
% 2.73/1.40  CNF conversion       : 0.03
% 2.73/1.40  Main loop            : 0.29
% 2.73/1.40  Inferencing          : 0.10
% 2.73/1.40  Reduction            : 0.09
% 2.73/1.40  Demodulation         : 0.06
% 2.73/1.40  BG Simplification    : 0.02
% 2.73/1.40  Subsumption          : 0.06
% 2.73/1.40  Abstraction          : 0.01
% 2.73/1.40  MUC search           : 0.00
% 2.73/1.41  Cooper               : 0.00
% 2.73/1.41  Total                : 0.65
% 2.73/1.41  Index Insertion      : 0.00
% 2.73/1.41  Index Deletion       : 0.00
% 2.73/1.41  Index Matching       : 0.00
% 2.73/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
