%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 179 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 455 expanded)
%              Number of equality atoms :   39 (  77 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_54,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_84,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1072,plain,(
    ! [B_142,A_143] :
      ( v2_tops_1(B_142,A_143)
      | k1_tops_1(A_143,B_142) != k1_xboole_0
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1091,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1072])).

tff(c_1102,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1091])).

tff(c_1103,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1102])).

tff(c_908,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(k1_tops_1(A_135,B_136),B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_922,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_908])).

tff(c_932,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_922])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1182,plain,(
    ! [A_147,B_148] :
      ( v3_pre_topc(k1_tops_1(A_147,B_148),A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1196,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1182])).

tff(c_1206,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1196])).

tff(c_127,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [A_71] : r1_tarski(A_71,A_71) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_99,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ m1_subset_1(A_65,k1_zfmisc_1(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_110,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_198,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,C_79)
      | ~ r1_tarski(B_80,C_79)
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_242,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_84,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_110,c_198])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_248,plain,(
    ! [A_6,A_84] :
      ( r1_tarski(A_6,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_6,A_84)
      | ~ r1_tarski(A_84,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_242,c_8])).

tff(c_935,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_932,c_248])).

tff(c_946,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_935])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,(
    ! [C_54] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_54
      | ~ v3_pre_topc(C_54,'#skF_2')
      | ~ r1_tarski(C_54,'#skF_3')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_549,plain,(
    ! [C_108] :
      ( k1_xboole_0 = C_108
      | ~ v3_pre_topc(C_108,'#skF_2')
      | ~ r1_tarski(C_108,'#skF_3')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_72])).

tff(c_1214,plain,(
    ! [A_150] :
      ( k1_xboole_0 = A_150
      | ~ v3_pre_topc(A_150,'#skF_2')
      | ~ r1_tarski(A_150,'#skF_3')
      | ~ r1_tarski(A_150,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_549])).

tff(c_1225,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_946,c_1214])).

tff(c_1258,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_1206,c_1225])).

tff(c_1260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1103,c_1258])).

tff(c_1261,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1716,plain,(
    ! [A_202,B_203] :
      ( k4_xboole_0(A_202,B_203) = k3_subset_1(A_202,B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(A_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1728,plain,(
    ! [A_26] : k4_xboole_0(A_26,k1_xboole_0) = k3_subset_1(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_1716])).

tff(c_1733,plain,(
    ! [A_26] : k3_subset_1(A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1728])).

tff(c_1696,plain,(
    ! [A_199,B_200] :
      ( k3_subset_1(A_199,k3_subset_1(A_199,B_200)) = B_200
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1708,plain,(
    ! [A_26] : k3_subset_1(A_26,k3_subset_1(A_26,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1696])).

tff(c_1734,plain,(
    ! [A_26] : k3_subset_1(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1733,c_1708])).

tff(c_1371,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_1'(A_167,B_168),A_167)
      | r1_tarski(A_167,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1376,plain,(
    ! [A_167] : r1_tarski(A_167,A_167) ),
    inference(resolution,[status(thm)],[c_1371,c_4])).

tff(c_1784,plain,(
    ! [B_206,A_207] :
      ( k4_xboole_0(B_206,A_207) = k3_subset_1(B_206,A_207)
      | ~ r1_tarski(A_207,B_206) ) ),
    inference(resolution,[status(thm)],[c_34,c_1716])).

tff(c_1796,plain,(
    ! [A_167] : k4_xboole_0(A_167,A_167) = k3_subset_1(A_167,A_167) ),
    inference(resolution,[status(thm)],[c_1376,c_1784])).

tff(c_1813,plain,(
    ! [A_167] : k4_xboole_0(A_167,A_167) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_1796])).

tff(c_1377,plain,(
    ! [A_169] : r1_tarski(A_169,A_169) ),
    inference(resolution,[status(thm)],[c_1371,c_4])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1381,plain,(
    ! [A_169] : k3_xboole_0(A_169,A_169) = A_169 ),
    inference(resolution,[status(thm)],[c_1377,c_10])).

tff(c_1262,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1264,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_56])).

tff(c_58,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1266,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_58])).

tff(c_60,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1289,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_60])).

tff(c_2657,plain,(
    ! [A_246,B_247] :
      ( k1_tops_1(A_246,B_247) = k1_xboole_0
      | ~ v2_tops_1(B_247,A_246)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2679,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2657])).

tff(c_2694,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1262,c_2679])).

tff(c_2805,plain,(
    ! [B_250,A_251,C_252] :
      ( r1_tarski(B_250,k1_tops_1(A_251,C_252))
      | ~ r1_tarski(B_250,C_252)
      | ~ v3_pre_topc(B_250,A_251)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2821,plain,(
    ! [B_250] :
      ( r1_tarski(B_250,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_250,'#skF_3')
      | ~ v3_pre_topc(B_250,'#skF_2')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_2805])).

tff(c_2923,plain,(
    ! [B_257] :
      ( r1_tarski(B_257,k1_xboole_0)
      | ~ r1_tarski(B_257,'#skF_3')
      | ~ v3_pre_topc(B_257,'#skF_2')
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2694,c_2821])).

tff(c_2942,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1289,c_2923])).

tff(c_2956,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1266,c_2942])).

tff(c_2991,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2956,c_10])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1330,plain,(
    ! [A_162,B_163] : k4_xboole_0(A_162,k4_xboole_0(A_162,B_163)) = k3_xboole_0(A_162,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1339,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1330])).

tff(c_3063,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4',k1_xboole_0)) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2991,c_1339])).

tff(c_3070,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1813,c_1381,c_14,c_3063])).

tff(c_3072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1261,c_3070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.80  
% 4.50/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.80  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.50/1.80  
% 4.50/1.80  %Foreground sorts:
% 4.50/1.80  
% 4.50/1.80  
% 4.50/1.80  %Background operators:
% 4.50/1.80  
% 4.50/1.80  
% 4.50/1.80  %Foreground operators:
% 4.50/1.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.80  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.50/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.50/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.50/1.80  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.50/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.50/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.50/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.50/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.80  
% 4.65/1.82  tff(f_141, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 4.65/1.82  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.65/1.82  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.65/1.82  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.65/1.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.65/1.82  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.65/1.82  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.65/1.82  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.65/1.82  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.65/1.82  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.65/1.82  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.65/1.82  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.65/1.82  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 4.65/1.82  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.65/1.82  tff(c_54, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_84, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 4.65/1.82  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_1072, plain, (![B_142, A_143]: (v2_tops_1(B_142, A_143) | k1_tops_1(A_143, B_142)!=k1_xboole_0 | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.65/1.82  tff(c_1091, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1072])).
% 4.65/1.82  tff(c_1102, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1091])).
% 4.65/1.82  tff(c_1103, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_1102])).
% 4.65/1.82  tff(c_908, plain, (![A_135, B_136]: (r1_tarski(k1_tops_1(A_135, B_136), B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.65/1.82  tff(c_922, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_908])).
% 4.65/1.82  tff(c_932, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_922])).
% 4.65/1.82  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_1182, plain, (![A_147, B_148]: (v3_pre_topc(k1_tops_1(A_147, B_148), A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.65/1.82  tff(c_1196, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1182])).
% 4.65/1.82  tff(c_1206, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1196])).
% 4.65/1.82  tff(c_127, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_132, plain, (![A_71]: (r1_tarski(A_71, A_71))), inference(resolution, [status(thm)], [c_127, c_4])).
% 4.65/1.82  tff(c_99, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~m1_subset_1(A_65, k1_zfmisc_1(B_66)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.65/1.82  tff(c_110, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_99])).
% 4.65/1.82  tff(c_198, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, C_79) | ~r1_tarski(B_80, C_79) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.65/1.82  tff(c_242, plain, (![A_84]: (r1_tarski(A_84, u1_struct_0('#skF_2')) | ~r1_tarski(A_84, '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_198])).
% 4.65/1.82  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.65/1.82  tff(c_248, plain, (![A_6, A_84]: (r1_tarski(A_6, u1_struct_0('#skF_2')) | ~r1_tarski(A_6, A_84) | ~r1_tarski(A_84, '#skF_3'))), inference(resolution, [status(thm)], [c_242, c_8])).
% 4.65/1.82  tff(c_935, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_932, c_248])).
% 4.65/1.82  tff(c_946, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_935])).
% 4.65/1.82  tff(c_34, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.65/1.82  tff(c_72, plain, (![C_54]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_54 | ~v3_pre_topc(C_54, '#skF_2') | ~r1_tarski(C_54, '#skF_3') | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_549, plain, (![C_108]: (k1_xboole_0=C_108 | ~v3_pre_topc(C_108, '#skF_2') | ~r1_tarski(C_108, '#skF_3') | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_84, c_72])).
% 4.65/1.82  tff(c_1214, plain, (![A_150]: (k1_xboole_0=A_150 | ~v3_pre_topc(A_150, '#skF_2') | ~r1_tarski(A_150, '#skF_3') | ~r1_tarski(A_150, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_549])).
% 4.65/1.82  tff(c_1225, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_946, c_1214])).
% 4.65/1.82  tff(c_1258, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_932, c_1206, c_1225])).
% 4.65/1.82  tff(c_1260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1103, c_1258])).
% 4.65/1.82  tff(c_1261, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 4.65/1.82  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.65/1.82  tff(c_30, plain, (![A_26]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.65/1.82  tff(c_1716, plain, (![A_202, B_203]: (k4_xboole_0(A_202, B_203)=k3_subset_1(A_202, B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(A_202)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.65/1.82  tff(c_1728, plain, (![A_26]: (k4_xboole_0(A_26, k1_xboole_0)=k3_subset_1(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_1716])).
% 4.65/1.82  tff(c_1733, plain, (![A_26]: (k3_subset_1(A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1728])).
% 4.65/1.82  tff(c_1696, plain, (![A_199, B_200]: (k3_subset_1(A_199, k3_subset_1(A_199, B_200))=B_200 | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.82  tff(c_1708, plain, (![A_26]: (k3_subset_1(A_26, k3_subset_1(A_26, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_1696])).
% 4.65/1.82  tff(c_1734, plain, (![A_26]: (k3_subset_1(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1733, c_1708])).
% 4.65/1.82  tff(c_1371, plain, (![A_167, B_168]: (r2_hidden('#skF_1'(A_167, B_168), A_167) | r1_tarski(A_167, B_168))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_1376, plain, (![A_167]: (r1_tarski(A_167, A_167))), inference(resolution, [status(thm)], [c_1371, c_4])).
% 4.65/1.82  tff(c_1784, plain, (![B_206, A_207]: (k4_xboole_0(B_206, A_207)=k3_subset_1(B_206, A_207) | ~r1_tarski(A_207, B_206))), inference(resolution, [status(thm)], [c_34, c_1716])).
% 4.65/1.82  tff(c_1796, plain, (![A_167]: (k4_xboole_0(A_167, A_167)=k3_subset_1(A_167, A_167))), inference(resolution, [status(thm)], [c_1376, c_1784])).
% 4.65/1.82  tff(c_1813, plain, (![A_167]: (k4_xboole_0(A_167, A_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_1796])).
% 4.65/1.82  tff(c_1377, plain, (![A_169]: (r1_tarski(A_169, A_169))), inference(resolution, [status(thm)], [c_1371, c_4])).
% 4.65/1.82  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.65/1.82  tff(c_1381, plain, (![A_169]: (k3_xboole_0(A_169, A_169)=A_169)), inference(resolution, [status(thm)], [c_1377, c_10])).
% 4.65/1.82  tff(c_1262, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 4.65/1.82  tff(c_56, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_1264, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_56])).
% 4.65/1.82  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_1266, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_58])).
% 4.65/1.82  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.65/1.82  tff(c_1289, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_60])).
% 4.65/1.82  tff(c_2657, plain, (![A_246, B_247]: (k1_tops_1(A_246, B_247)=k1_xboole_0 | ~v2_tops_1(B_247, A_246) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.65/1.82  tff(c_2679, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2657])).
% 4.65/1.82  tff(c_2694, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1262, c_2679])).
% 4.65/1.82  tff(c_2805, plain, (![B_250, A_251, C_252]: (r1_tarski(B_250, k1_tops_1(A_251, C_252)) | ~r1_tarski(B_250, C_252) | ~v3_pre_topc(B_250, A_251) | ~m1_subset_1(C_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.65/1.82  tff(c_2821, plain, (![B_250]: (r1_tarski(B_250, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_250, '#skF_3') | ~v3_pre_topc(B_250, '#skF_2') | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_2805])).
% 4.65/1.82  tff(c_2923, plain, (![B_257]: (r1_tarski(B_257, k1_xboole_0) | ~r1_tarski(B_257, '#skF_3') | ~v3_pre_topc(B_257, '#skF_2') | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2694, c_2821])).
% 4.65/1.82  tff(c_2942, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1289, c_2923])).
% 4.65/1.82  tff(c_2956, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_1266, c_2942])).
% 4.65/1.82  tff(c_2991, plain, (k3_xboole_0('#skF_4', k1_xboole_0)='#skF_4'), inference(resolution, [status(thm)], [c_2956, c_10])).
% 4.65/1.82  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.65/1.82  tff(c_1330, plain, (![A_162, B_163]: (k4_xboole_0(A_162, k4_xboole_0(A_162, B_163))=k3_xboole_0(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.65/1.82  tff(c_1339, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1330])).
% 4.65/1.82  tff(c_3063, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', k1_xboole_0))=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2991, c_1339])).
% 4.65/1.82  tff(c_3070, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1813, c_1381, c_14, c_3063])).
% 4.65/1.82  tff(c_3072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1261, c_3070])).
% 4.65/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.82  
% 4.65/1.82  Inference rules
% 4.65/1.82  ----------------------
% 4.65/1.82  #Ref     : 0
% 4.65/1.82  #Sup     : 691
% 4.65/1.82  #Fact    : 0
% 4.65/1.82  #Define  : 0
% 4.65/1.82  #Split   : 6
% 4.65/1.82  #Chain   : 0
% 4.65/1.82  #Close   : 0
% 4.65/1.82  
% 4.65/1.82  Ordering : KBO
% 4.65/1.82  
% 4.65/1.82  Simplification rules
% 4.65/1.82  ----------------------
% 4.65/1.82  #Subsume      : 61
% 4.65/1.82  #Demod        : 346
% 4.65/1.82  #Tautology    : 368
% 4.65/1.82  #SimpNegUnit  : 5
% 4.65/1.82  #BackRed      : 13
% 4.65/1.82  
% 4.65/1.82  #Partial instantiations: 0
% 4.65/1.82  #Strategies tried      : 1
% 4.65/1.82  
% 4.65/1.82  Timing (in seconds)
% 4.65/1.82  ----------------------
% 4.65/1.82  Preprocessing        : 0.35
% 4.65/1.82  Parsing              : 0.20
% 4.65/1.82  CNF conversion       : 0.02
% 4.65/1.82  Main loop            : 0.69
% 4.65/1.82  Inferencing          : 0.24
% 4.65/1.82  Reduction            : 0.23
% 4.65/1.82  Demodulation         : 0.16
% 4.65/1.82  BG Simplification    : 0.03
% 4.65/1.82  Subsumption          : 0.13
% 4.65/1.82  Abstraction          : 0.03
% 4.65/1.82  MUC search           : 0.00
% 4.65/1.82  Cooper               : 0.00
% 4.65/1.82  Total                : 1.08
% 4.65/1.82  Index Insertion      : 0.00
% 4.65/1.82  Index Deletion       : 0.00
% 4.65/1.82  Index Matching       : 0.00
% 4.65/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
