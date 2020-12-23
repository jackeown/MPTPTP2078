%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:50 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 255 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 811 expanded)
%              Number of equality atoms :   34 ( 123 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
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

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_396,plain,(
    ! [B_65,A_66] :
      ( v2_tops_1(B_65,A_66)
      | k1_tops_1(A_66,B_65) != k1_xboole_0
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_403,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_396])).

tff(c_407,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_403])).

tff(c_408,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_407])).

tff(c_58,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_227,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_232,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_227])).

tff(c_236,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_232])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_309,plain,(
    ! [A_60,B_61] :
      ( v3_pre_topc(k1_tops_1(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_314,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_309])).

tff(c_318,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_314])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_256,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_236,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_266,plain,(
    ! [C_5] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_5)
      | ~ r1_tarski('#skF_2',C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_8])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [C_33] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_33
      | ~ v3_pre_topc(C_33,'#skF_1')
      | ~ r1_tarski(C_33,'#skF_2')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_354,plain,(
    ! [C_63] :
      ( k1_xboole_0 = C_63
      | ~ v3_pre_topc(C_63,'#skF_1')
      | ~ r1_tarski(C_63,'#skF_2')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52])).

tff(c_807,plain,(
    ! [A_89] :
      ( k1_xboole_0 = A_89
      | ~ v3_pre_topc(A_89,'#skF_1')
      | ~ r1_tarski(A_89,'#skF_2')
      | ~ r1_tarski(A_89,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_354])).

tff(c_811,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_266,c_807])).

tff(c_831,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_236,c_318,c_811])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_831])).

tff(c_834,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_835,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_868,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_40])).

tff(c_1234,plain,(
    ! [A_117,B_118] :
      ( k1_tops_1(A_117,B_118) = k1_xboole_0
      | ~ v2_tops_1(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1237,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_1234])).

tff(c_1247,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1237])).

tff(c_1260,plain,(
    ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1247])).

tff(c_1424,plain,(
    ! [B_125,A_126] :
      ( v2_tops_1(B_125,A_126)
      | k1_tops_1(A_126,B_125) != k1_xboole_0
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1427,plain,
    ( v2_tops_1('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_1424])).

tff(c_1437,plain,
    ( v2_tops_1('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1427])).

tff(c_1438,plain,(
    k1_tops_1('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1260,c_1437])).

tff(c_1131,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(k1_tops_1(A_114,B_115),B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1133,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_1131])).

tff(c_1141,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1133])).

tff(c_1152,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1141,c_10])).

tff(c_1443,plain,(
    ! [C_127] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_127)
      | ~ r1_tarski('#skF_3',C_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1152,c_8])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1062,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1095,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1062])).

tff(c_1447,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1443,c_1095])).

tff(c_1455,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1438,c_1447])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_839,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_36])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_837,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_38])).

tff(c_1244,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1234])).

tff(c_1251,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_835,c_1244])).

tff(c_1699,plain,(
    ! [B_141,A_142,C_143] :
      ( r1_tarski(B_141,k1_tops_1(A_142,C_143))
      | ~ r1_tarski(B_141,C_143)
      | ~ v3_pre_topc(B_141,A_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1706,plain,(
    ! [B_141] :
      ( r1_tarski(B_141,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_141,'#skF_2')
      | ~ v3_pre_topc(B_141,'#skF_1')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1699])).

tff(c_1804,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k1_xboole_0)
      | ~ r1_tarski(B_148,'#skF_2')
      | ~ v3_pre_topc(B_148,'#skF_1')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1251,c_1706])).

tff(c_1807,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_1804])).

tff(c_1817,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_837,c_1807])).

tff(c_1819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_1817])).

tff(c_1820,plain,(
    k1_tops_1('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1247])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1151,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1141,c_2])).

tff(c_2134,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1820,c_1151])).

tff(c_2135,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_2134])).

tff(c_2167,plain,(
    ! [B_167,A_168,C_169] :
      ( r1_tarski(B_167,k1_tops_1(A_168,C_169))
      | ~ r1_tarski(B_167,C_169)
      | ~ v3_pre_topc(B_167,A_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2174,plain,(
    ! [B_167] :
      ( r1_tarski(B_167,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_167,'#skF_2')
      | ~ v3_pre_topc(B_167,'#skF_1')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_2167])).

tff(c_2318,plain,(
    ! [B_178] :
      ( r1_tarski(B_178,k1_xboole_0)
      | ~ r1_tarski(B_178,'#skF_2')
      | ~ v3_pre_topc(B_178,'#skF_1')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1251,c_2174])).

tff(c_2321,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_2318])).

tff(c_2331,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_837,c_2321])).

tff(c_2333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2135,c_2331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:59:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.72  
% 3.96/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.72  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.96/1.72  
% 3.96/1.72  %Foreground sorts:
% 3.96/1.72  
% 3.96/1.72  
% 3.96/1.72  %Background operators:
% 3.96/1.72  
% 3.96/1.72  
% 3.96/1.72  %Foreground operators:
% 3.96/1.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.72  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.96/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.96/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.72  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.96/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.96/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.96/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.72  
% 3.96/1.74  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.96/1.74  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.96/1.74  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.96/1.74  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.96/1.74  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.96/1.74  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.96/1.74  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.96/1.74  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.96/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.96/1.74  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.96/1.74  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_56, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 3.96/1.74  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_396, plain, (![B_65, A_66]: (v2_tops_1(B_65, A_66) | k1_tops_1(A_66, B_65)!=k1_xboole_0 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.74  tff(c_403, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_396])).
% 3.96/1.74  tff(c_407, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_403])).
% 3.96/1.74  tff(c_408, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_407])).
% 3.96/1.74  tff(c_58, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/1.74  tff(c_66, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_58])).
% 3.96/1.74  tff(c_227, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.74  tff(c_232, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_227])).
% 3.96/1.74  tff(c_236, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_232])).
% 3.96/1.74  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_309, plain, (![A_60, B_61]: (v3_pre_topc(k1_tops_1(A_60, B_61), A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.96/1.74  tff(c_314, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_309])).
% 3.96/1.74  tff(c_318, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_314])).
% 3.96/1.74  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.74  tff(c_256, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_236, c_10])).
% 3.96/1.74  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/1.74  tff(c_266, plain, (![C_5]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_5) | ~r1_tarski('#skF_2', C_5))), inference(superposition, [status(thm), theory('equality')], [c_256, c_8])).
% 3.96/1.74  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/1.74  tff(c_52, plain, (![C_33]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_33 | ~v3_pre_topc(C_33, '#skF_1') | ~r1_tarski(C_33, '#skF_2') | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_354, plain, (![C_63]: (k1_xboole_0=C_63 | ~v3_pre_topc(C_63, '#skF_1') | ~r1_tarski(C_63, '#skF_2') | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_52])).
% 3.96/1.74  tff(c_807, plain, (![A_89]: (k1_xboole_0=A_89 | ~v3_pre_topc(A_89, '#skF_1') | ~r1_tarski(A_89, '#skF_2') | ~r1_tarski(A_89, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_354])).
% 3.96/1.74  tff(c_811, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_266, c_807])).
% 3.96/1.74  tff(c_831, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_236, c_318, c_811])).
% 3.96/1.74  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_831])).
% 3.96/1.74  tff(c_834, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.96/1.74  tff(c_835, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.96/1.74  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_868, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_40])).
% 3.96/1.74  tff(c_1234, plain, (![A_117, B_118]: (k1_tops_1(A_117, B_118)=k1_xboole_0 | ~v2_tops_1(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.74  tff(c_1237, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_868, c_1234])).
% 3.96/1.74  tff(c_1247, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1237])).
% 3.96/1.74  tff(c_1260, plain, (~v2_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1247])).
% 3.96/1.74  tff(c_1424, plain, (![B_125, A_126]: (v2_tops_1(B_125, A_126) | k1_tops_1(A_126, B_125)!=k1_xboole_0 | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.74  tff(c_1427, plain, (v2_tops_1('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_868, c_1424])).
% 3.96/1.74  tff(c_1437, plain, (v2_tops_1('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1427])).
% 3.96/1.74  tff(c_1438, plain, (k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1260, c_1437])).
% 3.96/1.74  tff(c_1131, plain, (![A_114, B_115]: (r1_tarski(k1_tops_1(A_114, B_115), B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.74  tff(c_1133, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_868, c_1131])).
% 3.96/1.74  tff(c_1141, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1133])).
% 3.96/1.74  tff(c_1152, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1141, c_10])).
% 3.96/1.74  tff(c_1443, plain, (![C_127]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_127) | ~r1_tarski('#skF_3', C_127))), inference(superposition, [status(thm), theory('equality')], [c_1152, c_8])).
% 3.96/1.74  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.96/1.74  tff(c_1062, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.74  tff(c_1095, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1062])).
% 3.96/1.74  tff(c_1447, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1443, c_1095])).
% 3.96/1.74  tff(c_1455, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1438, c_1447])).
% 3.96/1.74  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_839, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_36])).
% 3.96/1.74  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.96/1.74  tff(c_837, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_38])).
% 3.96/1.74  tff(c_1244, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1234])).
% 3.96/1.74  tff(c_1251, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_835, c_1244])).
% 3.96/1.74  tff(c_1699, plain, (![B_141, A_142, C_143]: (r1_tarski(B_141, k1_tops_1(A_142, C_143)) | ~r1_tarski(B_141, C_143) | ~v3_pre_topc(B_141, A_142) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.74  tff(c_1706, plain, (![B_141]: (r1_tarski(B_141, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_141, '#skF_2') | ~v3_pre_topc(B_141, '#skF_1') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1699])).
% 3.96/1.74  tff(c_1804, plain, (![B_148]: (r1_tarski(B_148, k1_xboole_0) | ~r1_tarski(B_148, '#skF_2') | ~v3_pre_topc(B_148, '#skF_1') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1251, c_1706])).
% 3.96/1.74  tff(c_1807, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_868, c_1804])).
% 3.96/1.74  tff(c_1817, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_839, c_837, c_1807])).
% 3.96/1.74  tff(c_1819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1455, c_1817])).
% 3.96/1.74  tff(c_1820, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1247])).
% 3.96/1.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.74  tff(c_1151, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1141, c_2])).
% 3.96/1.74  tff(c_2134, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1820, c_1151])).
% 3.96/1.74  tff(c_2135, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_834, c_2134])).
% 3.96/1.74  tff(c_2167, plain, (![B_167, A_168, C_169]: (r1_tarski(B_167, k1_tops_1(A_168, C_169)) | ~r1_tarski(B_167, C_169) | ~v3_pre_topc(B_167, A_168) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.74  tff(c_2174, plain, (![B_167]: (r1_tarski(B_167, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_167, '#skF_2') | ~v3_pre_topc(B_167, '#skF_1') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_2167])).
% 3.96/1.74  tff(c_2318, plain, (![B_178]: (r1_tarski(B_178, k1_xboole_0) | ~r1_tarski(B_178, '#skF_2') | ~v3_pre_topc(B_178, '#skF_1') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1251, c_2174])).
% 3.96/1.74  tff(c_2321, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_868, c_2318])).
% 3.96/1.74  tff(c_2331, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_839, c_837, c_2321])).
% 3.96/1.74  tff(c_2333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2135, c_2331])).
% 3.96/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.74  
% 3.96/1.74  Inference rules
% 3.96/1.74  ----------------------
% 3.96/1.74  #Ref     : 0
% 3.96/1.74  #Sup     : 513
% 3.96/1.74  #Fact    : 0
% 3.96/1.74  #Define  : 0
% 3.96/1.74  #Split   : 12
% 3.96/1.74  #Chain   : 0
% 3.96/1.74  #Close   : 0
% 3.96/1.74  
% 3.96/1.74  Ordering : KBO
% 3.96/1.74  
% 3.96/1.74  Simplification rules
% 3.96/1.74  ----------------------
% 3.96/1.74  #Subsume      : 39
% 3.96/1.74  #Demod        : 378
% 3.96/1.74  #Tautology    : 297
% 3.96/1.74  #SimpNegUnit  : 11
% 3.96/1.74  #BackRed      : 8
% 3.96/1.74  
% 3.96/1.74  #Partial instantiations: 0
% 3.96/1.74  #Strategies tried      : 1
% 3.96/1.74  
% 3.96/1.74  Timing (in seconds)
% 3.96/1.74  ----------------------
% 3.96/1.74  Preprocessing        : 0.31
% 3.96/1.74  Parsing              : 0.17
% 3.96/1.74  CNF conversion       : 0.02
% 3.96/1.74  Main loop            : 0.63
% 3.96/1.74  Inferencing          : 0.21
% 3.96/1.74  Reduction            : 0.23
% 3.96/1.74  Demodulation         : 0.17
% 3.96/1.74  BG Simplification    : 0.02
% 3.96/1.74  Subsumption          : 0.11
% 3.96/1.74  Abstraction          : 0.03
% 3.96/1.74  MUC search           : 0.00
% 3.96/1.74  Cooper               : 0.00
% 3.96/1.74  Total                : 1.00
% 3.96/1.74  Index Insertion      : 0.00
% 3.96/1.74  Index Deletion       : 0.00
% 3.96/1.74  Index Matching       : 0.00
% 3.96/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
