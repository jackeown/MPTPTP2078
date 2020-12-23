%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 19.57s
% Output     : CNFRefutation 19.67s
% Verified   : 
% Statistics : Number of formulae       :  145 (1482 expanded)
%              Number of leaves         :   34 ( 511 expanded)
%              Depth                    :   25
%              Number of atoms          :  277 (2970 expanded)
%              Number of equality atoms :   31 ( 345 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_36,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    ! [A_20] :
      ( v1_tops_1('#skF_1'(A_20),A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_64,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_49] : r1_tarski(A_49,A_49) ),
    inference(resolution,[status(thm)],[c_45,c_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_49] : k2_xboole_0(A_49,A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_267,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(B_65,k2_pre_topc(A_66,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_283,plain,(
    ! [A_66] :
      ( r1_tarski(u1_struct_0(A_66),k2_pre_topc(A_66,u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_45,c_267])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_75,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,k2_xboole_0(A_60,B_61))
      | ~ r1_tarski(A_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_550,plain,(
    ! [A_87,A_88,B_89,A_90] :
      ( r1_tarski(A_87,k2_xboole_0(A_88,B_89))
      | ~ r1_tarski(A_87,A_90)
      | ~ r1_tarski(A_90,A_88) ) ),
    inference(resolution,[status(thm)],[c_167,c_4])).

tff(c_587,plain,(
    ! [A_91,B_92] :
      ( r1_tarski('#skF_3',k2_xboole_0(A_91,B_92))
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_91) ) ),
    inference(resolution,[status(thm)],[c_75,c_550])).

tff(c_596,plain,(
    ! [B_92] :
      ( r1_tarski('#skF_3',k2_xboole_0(k2_pre_topc('#skF_2',u1_struct_0('#skF_2')),B_92))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_283,c_587])).

tff(c_660,plain,(
    ! [B_94] : r1_tarski('#skF_3',k2_xboole_0(k2_pre_topc('#skF_2',u1_struct_0('#skF_2')),B_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_596])).

tff(c_687,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2',u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_660])).

tff(c_739,plain,(
    k2_xboole_0('#skF_3',k2_pre_topc('#skF_2',u1_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_687,c_2])).

tff(c_341,plain,(
    ! [A_70] :
      ( r1_tarski(u1_struct_0(A_70),k2_pre_topc(A_70,u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_45,c_267])).

tff(c_8108,plain,(
    ! [A_356] :
      ( k2_xboole_0(u1_struct_0(A_356),k2_pre_topc(A_356,u1_struct_0(A_356))) = k2_pre_topc(A_356,u1_struct_0(A_356))
      | ~ l1_pre_topc(A_356) ) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_76,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_45,c_64])).

tff(c_622,plain,(
    ! [B_93] : r1_tarski('#skF_3',k2_xboole_0(u1_struct_0('#skF_2'),B_93)) ),
    inference(resolution,[status(thm)],[c_76,c_587])).

tff(c_656,plain,(
    ! [B_93] : k2_xboole_0('#skF_3',k2_xboole_0(u1_struct_0('#skF_2'),B_93)) = k2_xboole_0(u1_struct_0('#skF_2'),B_93) ),
    inference(resolution,[status(thm)],[c_622,c_2])).

tff(c_8192,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',u1_struct_0('#skF_2'))) = k2_xboole_0('#skF_3',k2_pre_topc('#skF_2',u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8108,c_656])).

tff(c_8252,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',u1_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_739,c_8192])).

tff(c_99,plain,(
    ! [A_51] :
      ( m1_subset_1('#skF_1'(A_51),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ! [A_52] :
      ( r1_tarski('#skF_1'(A_52),u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_99,c_12])).

tff(c_116,plain,(
    ! [A_52] :
      ( k2_xboole_0('#skF_1'(A_52),u1_struct_0(A_52)) = u1_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_858,plain,(
    ! [A_102,A_103,B_104,B_105] :
      ( r1_tarski(A_102,k2_xboole_0(A_103,B_104))
      | ~ r1_tarski(k2_xboole_0(A_102,B_105),A_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_550])).

tff(c_909,plain,(
    ! [A_106,B_107,B_108] : r1_tarski(A_106,k2_xboole_0(k2_xboole_0(A_106,B_107),B_108)) ),
    inference(resolution,[status(thm)],[c_76,c_858])).

tff(c_946,plain,(
    ! [A_52,B_108] :
      ( r1_tarski('#skF_1'(A_52),k2_xboole_0(u1_struct_0(A_52),B_108))
      | ~ l1_pre_topc(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_909])).

tff(c_8406,plain,
    ( r1_tarski('#skF_1'('#skF_2'),k2_pre_topc('#skF_2',u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8252,c_946])).

tff(c_8468,plain,(
    r1_tarski('#skF_1'('#skF_2'),k2_pre_topc('#skF_2',u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8406])).

tff(c_395,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k2_pre_topc(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3219,plain,(
    ! [A_200,B_201] :
      ( r1_tarski(k2_pre_topc(A_200,B_201),u1_struct_0(A_200))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_395,c_12])).

tff(c_10644,plain,(
    ! [A_392,A_393,B_394] :
      ( r1_tarski(A_392,u1_struct_0(A_393))
      | ~ r1_tarski(A_392,k2_pre_topc(A_393,B_394))
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393) ) ),
    inference(resolution,[status(thm)],[c_3219,c_4])).

tff(c_10658,plain,
    ( r1_tarski('#skF_1'('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8468,c_10644])).

tff(c_10720,plain,(
    r1_tarski('#skF_1'('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45,c_10658])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_697,plain,(
    ! [A_95,B_96] :
      ( k2_pre_topc(A_95,B_96) = k2_struct_0(A_95)
      | ~ v1_tops_1(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_717,plain,(
    ! [A_95,A_10] :
      ( k2_pre_topc(A_95,A_10) = k2_struct_0(A_95)
      | ~ v1_tops_1(A_10,A_95)
      | ~ l1_pre_topc(A_95)
      | ~ r1_tarski(A_10,u1_struct_0(A_95)) ) ),
    inference(resolution,[status(thm)],[c_14,c_697])).

tff(c_10783,plain,
    ( k2_pre_topc('#skF_2','#skF_1'('#skF_2')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_1'('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10720,c_717])).

tff(c_10812,plain,
    ( k2_pre_topc('#skF_2','#skF_1'('#skF_2')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_1'('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10783])).

tff(c_11999,plain,(
    ~ v1_tops_1('#skF_1'('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_10812])).

tff(c_12005,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_11999])).

tff(c_12010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12005])).

tff(c_12011,plain,(
    k2_pre_topc('#skF_2','#skF_1'('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_10812])).

tff(c_26,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_1'(A_20),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10276,plain,(
    ! [A_388,B_389] :
      ( k2_xboole_0(k2_pre_topc(A_388,B_389),u1_struct_0(A_388)) = u1_struct_0(A_388)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_pre_topc(A_388) ) ),
    inference(resolution,[status(thm)],[c_3219,c_2])).

tff(c_13769,plain,(
    ! [A_435] :
      ( k2_xboole_0(k2_pre_topc(A_435,'#skF_1'(A_435)),u1_struct_0(A_435)) = u1_struct_0(A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(resolution,[status(thm)],[c_26,c_10276])).

tff(c_13886,plain,
    ( k2_xboole_0(k2_struct_0('#skF_2'),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12011,c_13769])).

tff(c_13904,plain,(
    k2_xboole_0(k2_struct_0('#skF_2'),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13886])).

tff(c_14018,plain,(
    r1_tarski(k2_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13904,c_6])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    ! [A_22] :
      ( k1_tops_1(A_22,k2_struct_0(A_22)) = k2_struct_0(A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1929,plain,(
    ! [C_143,A_144,B_145] :
      ( m2_connsp_2(C_143,A_144,B_145)
      | ~ r1_tarski(B_145,k1_tops_1(A_144,C_143))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7523,plain,(
    ! [A_343,B_344] :
      ( m2_connsp_2(k2_struct_0(A_343),A_343,B_344)
      | ~ r1_tarski(B_344,k2_struct_0(A_343))
      | ~ m1_subset_1(k2_struct_0(A_343),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_subset_1(B_344,k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1929])).

tff(c_19530,plain,(
    ! [A_510,B_511] :
      ( m2_connsp_2(k2_struct_0(A_510),A_510,B_511)
      | ~ r1_tarski(B_511,k2_struct_0(A_510))
      | ~ m1_subset_1(B_511,k1_zfmisc_1(u1_struct_0(A_510)))
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | ~ r1_tarski(k2_struct_0(A_510),u1_struct_0(A_510)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7523])).

tff(c_19539,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski(k2_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_19530])).

tff(c_19548,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14018,c_42,c_40,c_19539])).

tff(c_19549,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_19548])).

tff(c_403,plain,(
    ! [A_78,A_79] :
      ( r1_tarski(A_78,k2_pre_topc(A_79,A_78))
      | ~ l1_pre_topc(A_79)
      | ~ r1_tarski(A_78,u1_struct_0(A_79)) ) ),
    inference(resolution,[status(thm)],[c_14,c_267])).

tff(c_412,plain,(
    ! [A_3,A_79,A_78] :
      ( r1_tarski(A_3,k2_pre_topc(A_79,A_78))
      | ~ r1_tarski(A_3,A_78)
      | ~ l1_pre_topc(A_79)
      | ~ r1_tarski(A_78,u1_struct_0(A_79)) ) ),
    inference(resolution,[status(thm)],[c_403,c_4])).

tff(c_14052,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_2',k2_struct_0('#skF_2')))
      | ~ r1_tarski(A_3,k2_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14018,c_412])).

tff(c_14087,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_pre_topc('#skF_2',k2_struct_0('#skF_2')))
      | ~ r1_tarski(A_3,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14052])).

tff(c_156,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_75,c_146])).

tff(c_8836,plain,(
    ! [A_365,A_366] :
      ( k2_xboole_0(A_365,k2_pre_topc(A_366,A_365)) = k2_pre_topc(A_366,A_365)
      | ~ l1_pre_topc(A_366)
      | ~ r1_tarski(A_365,u1_struct_0(A_366)) ) ),
    inference(resolution,[status(thm)],[c_403,c_2])).

tff(c_8846,plain,(
    ! [A_55] :
      ( k2_xboole_0(A_55,k2_pre_topc('#skF_2',A_55)) = k2_pre_topc('#skF_2',A_55)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_156,c_8836])).

tff(c_9042,plain,(
    ! [A_371] :
      ( k2_xboole_0(A_371,k2_pre_topc('#skF_2',A_371)) = k2_pre_topc('#skF_2',A_371)
      | ~ r1_tarski(A_371,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8846])).

tff(c_9484,plain,(
    ! [A_371] :
      ( r1_tarski(A_371,k2_pre_topc('#skF_2',A_371))
      | ~ r1_tarski(A_371,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9042,c_6])).

tff(c_10285,plain,
    ( k2_xboole_0(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_10276])).

tff(c_10294,plain,(
    k2_xboole_0(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10285])).

tff(c_586,plain,(
    ! [A_6,A_88,B_89,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(A_88,B_89))
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_550])).

tff(c_11402,plain,(
    ! [A_403,B_404] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),k2_xboole_0(A_403,B_404))
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10294,c_586])).

tff(c_11510,plain,(
    ! [A_405] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),A_405)
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_11402])).

tff(c_26659,plain,(
    ! [A_620,A_621] :
      ( r1_tarski(A_620,A_621)
      | ~ r1_tarski(A_620,k2_pre_topc('#skF_2','#skF_3'))
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_621) ) ),
    inference(resolution,[status(thm)],[c_11510,c_4])).

tff(c_26670,plain,(
    ! [A_621] :
      ( r1_tarski('#skF_3',A_621)
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_621)
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_9484,c_26659])).

tff(c_26701,plain,(
    ! [A_622] :
      ( r1_tarski('#skF_3',A_622)
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_622) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26670])).

tff(c_26962,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2',k2_struct_0('#skF_2')))
    | ~ r1_tarski(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14087,c_26701])).

tff(c_27441,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26962])).

tff(c_12012,plain,(
    v1_tops_1('#skF_1'('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_10812])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_pre_topc(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12197,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12011,c_16])).

tff(c_12235,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12197])).

tff(c_37777,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_12235])).

tff(c_37780,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_37777])).

tff(c_37787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37780])).

tff(c_37789,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_12235])).

tff(c_103,plain,(
    ! [A_51] :
      ( r1_tarski('#skF_1'(A_51),u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_99,c_12])).

tff(c_1333,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_tops_1(C_126,A_127)
      | ~ r1_tarski(B_128,C_126)
      | ~ v1_tops_1(B_128,A_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22346,plain,(
    ! [A_556,A_557] :
      ( v1_tops_1(u1_struct_0(A_556),A_557)
      | ~ v1_tops_1('#skF_1'(A_556),A_557)
      | ~ m1_subset_1(u1_struct_0(A_556),k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ m1_subset_1('#skF_1'(A_556),k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557)
      | ~ l1_pre_topc(A_556) ) ),
    inference(resolution,[status(thm)],[c_103,c_1333])).

tff(c_54754,plain,(
    ! [A_952] :
      ( v1_tops_1(u1_struct_0(A_952),A_952)
      | ~ v1_tops_1('#skF_1'(A_952),A_952)
      | ~ m1_subset_1('#skF_1'(A_952),k1_zfmisc_1(u1_struct_0(A_952)))
      | ~ l1_pre_topc(A_952) ) ),
    inference(resolution,[status(thm)],[c_45,c_22346])).

tff(c_54757,plain,
    ( v1_tops_1(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tops_1('#skF_1'('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_37789,c_54754])).

tff(c_54766,plain,(
    v1_tops_1(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12012,c_54757])).

tff(c_721,plain,(
    ! [A_95] :
      ( k2_pre_topc(A_95,u1_struct_0(A_95)) = k2_struct_0(A_95)
      | ~ v1_tops_1(u1_struct_0(A_95),A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_45,c_697])).

tff(c_54774,plain,
    ( k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54766,c_721])).

tff(c_54778,plain,(
    k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_54774])).

tff(c_8438,plain,(
    r1_tarski(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8252,c_6])).

tff(c_54831,plain,(
    r1_tarski(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54778,c_8438])).

tff(c_54861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27441,c_54831])).

tff(c_54863,plain,(
    r1_tarski(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26962])).

tff(c_26692,plain,(
    ! [A_621] :
      ( r1_tarski('#skF_3',A_621)
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26670])).

tff(c_54871,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54863,c_26692])).

tff(c_54929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19549,c_54871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.57/10.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.67/10.87  
% 19.67/10.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.67/10.87  %$ m2_connsp_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 19.67/10.87  
% 19.67/10.87  %Foreground sorts:
% 19.67/10.87  
% 19.67/10.87  
% 19.67/10.87  %Background operators:
% 19.67/10.87  
% 19.67/10.87  
% 19.67/10.87  %Foreground operators:
% 19.67/10.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.67/10.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.67/10.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 19.67/10.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.67/10.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.67/10.87  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 19.67/10.87  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 19.67/10.87  tff('#skF_2', type, '#skF_2': $i).
% 19.67/10.87  tff('#skF_3', type, '#skF_3': $i).
% 19.67/10.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.67/10.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.67/10.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.67/10.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.67/10.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.67/10.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.67/10.87  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.67/10.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 19.67/10.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 19.67/10.87  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 19.67/10.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.67/10.87  
% 19.67/10.89  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 19.67/10.89  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_tops_1)).
% 19.67/10.89  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 19.67/10.89  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 19.67/10.89  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 19.67/10.89  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 19.67/10.89  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 19.67/10.89  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 19.67/10.89  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 19.67/10.89  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 19.67/10.89  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 19.67/10.89  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 19.67/10.89  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 19.67/10.89  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 19.67/10.89  tff(c_36, plain, (~m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.67/10.89  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.67/10.89  tff(c_24, plain, (![A_20]: (v1_tops_1('#skF_1'(A_20), A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.67/10.89  tff(c_8, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.67/10.89  tff(c_10, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.67/10.89  tff(c_45, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 19.67/10.89  tff(c_64, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.67/10.89  tff(c_77, plain, (![A_49]: (r1_tarski(A_49, A_49))), inference(resolution, [status(thm)], [c_45, c_64])).
% 19.67/10.89  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.67/10.89  tff(c_81, plain, (![A_49]: (k2_xboole_0(A_49, A_49)=A_49)), inference(resolution, [status(thm)], [c_77, c_2])).
% 19.67/10.89  tff(c_267, plain, (![B_65, A_66]: (r1_tarski(B_65, k2_pre_topc(A_66, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.67/10.89  tff(c_283, plain, (![A_66]: (r1_tarski(u1_struct_0(A_66), k2_pre_topc(A_66, u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_45, c_267])).
% 19.67/10.89  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.67/10.89  tff(c_75, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_64])).
% 19.67/10.89  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.67/10.89  tff(c_146, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.67/10.89  tff(c_167, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, k2_xboole_0(A_60, B_61)) | ~r1_tarski(A_59, A_60))), inference(resolution, [status(thm)], [c_6, c_146])).
% 19.67/10.89  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.67/10.89  tff(c_550, plain, (![A_87, A_88, B_89, A_90]: (r1_tarski(A_87, k2_xboole_0(A_88, B_89)) | ~r1_tarski(A_87, A_90) | ~r1_tarski(A_90, A_88))), inference(resolution, [status(thm)], [c_167, c_4])).
% 19.67/10.89  tff(c_587, plain, (![A_91, B_92]: (r1_tarski('#skF_3', k2_xboole_0(A_91, B_92)) | ~r1_tarski(u1_struct_0('#skF_2'), A_91))), inference(resolution, [status(thm)], [c_75, c_550])).
% 19.67/10.89  tff(c_596, plain, (![B_92]: (r1_tarski('#skF_3', k2_xboole_0(k2_pre_topc('#skF_2', u1_struct_0('#skF_2')), B_92)) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_283, c_587])).
% 19.67/10.89  tff(c_660, plain, (![B_94]: (r1_tarski('#skF_3', k2_xboole_0(k2_pre_topc('#skF_2', u1_struct_0('#skF_2')), B_94)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_596])).
% 19.67/10.89  tff(c_687, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_81, c_660])).
% 19.67/10.89  tff(c_739, plain, (k2_xboole_0('#skF_3', k2_pre_topc('#skF_2', u1_struct_0('#skF_2')))=k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_687, c_2])).
% 19.67/10.89  tff(c_341, plain, (![A_70]: (r1_tarski(u1_struct_0(A_70), k2_pre_topc(A_70, u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_45, c_267])).
% 19.67/10.89  tff(c_8108, plain, (![A_356]: (k2_xboole_0(u1_struct_0(A_356), k2_pre_topc(A_356, u1_struct_0(A_356)))=k2_pre_topc(A_356, u1_struct_0(A_356)) | ~l1_pre_topc(A_356))), inference(resolution, [status(thm)], [c_341, c_2])).
% 19.67/10.89  tff(c_76, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_45, c_64])).
% 19.67/10.89  tff(c_622, plain, (![B_93]: (r1_tarski('#skF_3', k2_xboole_0(u1_struct_0('#skF_2'), B_93)))), inference(resolution, [status(thm)], [c_76, c_587])).
% 19.67/10.89  tff(c_656, plain, (![B_93]: (k2_xboole_0('#skF_3', k2_xboole_0(u1_struct_0('#skF_2'), B_93))=k2_xboole_0(u1_struct_0('#skF_2'), B_93))), inference(resolution, [status(thm)], [c_622, c_2])).
% 19.67/10.89  tff(c_8192, plain, (k2_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', u1_struct_0('#skF_2')))=k2_xboole_0('#skF_3', k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8108, c_656])).
% 19.67/10.89  tff(c_8252, plain, (k2_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', u1_struct_0('#skF_2')))=k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_739, c_8192])).
% 19.67/10.89  tff(c_99, plain, (![A_51]: (m1_subset_1('#skF_1'(A_51), k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.67/10.89  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.67/10.89  tff(c_112, plain, (![A_52]: (r1_tarski('#skF_1'(A_52), u1_struct_0(A_52)) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_99, c_12])).
% 19.67/10.89  tff(c_116, plain, (![A_52]: (k2_xboole_0('#skF_1'(A_52), u1_struct_0(A_52))=u1_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_112, c_2])).
% 19.67/10.89  tff(c_858, plain, (![A_102, A_103, B_104, B_105]: (r1_tarski(A_102, k2_xboole_0(A_103, B_104)) | ~r1_tarski(k2_xboole_0(A_102, B_105), A_103))), inference(resolution, [status(thm)], [c_6, c_550])).
% 19.67/10.89  tff(c_909, plain, (![A_106, B_107, B_108]: (r1_tarski(A_106, k2_xboole_0(k2_xboole_0(A_106, B_107), B_108)))), inference(resolution, [status(thm)], [c_76, c_858])).
% 19.67/10.89  tff(c_946, plain, (![A_52, B_108]: (r1_tarski('#skF_1'(A_52), k2_xboole_0(u1_struct_0(A_52), B_108)) | ~l1_pre_topc(A_52))), inference(superposition, [status(thm), theory('equality')], [c_116, c_909])).
% 19.67/10.89  tff(c_8406, plain, (r1_tarski('#skF_1'('#skF_2'), k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8252, c_946])).
% 19.67/10.89  tff(c_8468, plain, (r1_tarski('#skF_1'('#skF_2'), k2_pre_topc('#skF_2', u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8406])).
% 19.67/10.89  tff(c_395, plain, (![A_76, B_77]: (m1_subset_1(k2_pre_topc(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.67/10.89  tff(c_3219, plain, (![A_200, B_201]: (r1_tarski(k2_pre_topc(A_200, B_201), u1_struct_0(A_200)) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(resolution, [status(thm)], [c_395, c_12])).
% 19.67/10.89  tff(c_10644, plain, (![A_392, A_393, B_394]: (r1_tarski(A_392, u1_struct_0(A_393)) | ~r1_tarski(A_392, k2_pre_topc(A_393, B_394)) | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393))), inference(resolution, [status(thm)], [c_3219, c_4])).
% 19.67/10.89  tff(c_10658, plain, (r1_tarski('#skF_1'('#skF_2'), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8468, c_10644])).
% 19.67/10.89  tff(c_10720, plain, (r1_tarski('#skF_1'('#skF_2'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_45, c_10658])).
% 19.67/10.89  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.67/10.89  tff(c_697, plain, (![A_95, B_96]: (k2_pre_topc(A_95, B_96)=k2_struct_0(A_95) | ~v1_tops_1(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_67])).
% 19.67/10.89  tff(c_717, plain, (![A_95, A_10]: (k2_pre_topc(A_95, A_10)=k2_struct_0(A_95) | ~v1_tops_1(A_10, A_95) | ~l1_pre_topc(A_95) | ~r1_tarski(A_10, u1_struct_0(A_95)))), inference(resolution, [status(thm)], [c_14, c_697])).
% 19.67/10.89  tff(c_10783, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_1'('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10720, c_717])).
% 19.67/10.89  tff(c_10812, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_1'('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10783])).
% 19.67/10.89  tff(c_11999, plain, (~v1_tops_1('#skF_1'('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_10812])).
% 19.67/10.89  tff(c_12005, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_11999])).
% 19.67/10.89  tff(c_12010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_12005])).
% 19.67/10.89  tff(c_12011, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_10812])).
% 19.67/10.89  tff(c_26, plain, (![A_20]: (m1_subset_1('#skF_1'(A_20), k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.67/10.89  tff(c_10276, plain, (![A_388, B_389]: (k2_xboole_0(k2_pre_topc(A_388, B_389), u1_struct_0(A_388))=u1_struct_0(A_388) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_pre_topc(A_388))), inference(resolution, [status(thm)], [c_3219, c_2])).
% 19.67/10.89  tff(c_13769, plain, (![A_435]: (k2_xboole_0(k2_pre_topc(A_435, '#skF_1'(A_435)), u1_struct_0(A_435))=u1_struct_0(A_435) | ~l1_pre_topc(A_435))), inference(resolution, [status(thm)], [c_26, c_10276])).
% 19.67/10.89  tff(c_13886, plain, (k2_xboole_0(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12011, c_13769])).
% 19.67/10.89  tff(c_13904, plain, (k2_xboole_0(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_13886])).
% 19.67/10.89  tff(c_14018, plain, (r1_tarski(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13904, c_6])).
% 19.67/10.89  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.67/10.89  tff(c_28, plain, (![A_22]: (k1_tops_1(A_22, k2_struct_0(A_22))=k2_struct_0(A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.67/10.89  tff(c_1929, plain, (![C_143, A_144, B_145]: (m2_connsp_2(C_143, A_144, B_145) | ~r1_tarski(B_145, k1_tops_1(A_144, C_143)) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_108])).
% 19.67/10.89  tff(c_7523, plain, (![A_343, B_344]: (m2_connsp_2(k2_struct_0(A_343), A_343, B_344) | ~r1_tarski(B_344, k2_struct_0(A_343)) | ~m1_subset_1(k2_struct_0(A_343), k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_subset_1(B_344, k1_zfmisc_1(u1_struct_0(A_343))) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1929])).
% 19.67/10.89  tff(c_19530, plain, (![A_510, B_511]: (m2_connsp_2(k2_struct_0(A_510), A_510, B_511) | ~r1_tarski(B_511, k2_struct_0(A_510)) | ~m1_subset_1(B_511, k1_zfmisc_1(u1_struct_0(A_510))) | ~l1_pre_topc(A_510) | ~v2_pre_topc(A_510) | ~r1_tarski(k2_struct_0(A_510), u1_struct_0(A_510)))), inference(resolution, [status(thm)], [c_14, c_7523])).
% 19.67/10.89  tff(c_19539, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(k2_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_19530])).
% 19.67/10.89  tff(c_19548, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14018, c_42, c_40, c_19539])).
% 19.67/10.89  tff(c_19549, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_19548])).
% 19.67/10.89  tff(c_403, plain, (![A_78, A_79]: (r1_tarski(A_78, k2_pre_topc(A_79, A_78)) | ~l1_pre_topc(A_79) | ~r1_tarski(A_78, u1_struct_0(A_79)))), inference(resolution, [status(thm)], [c_14, c_267])).
% 19.67/10.89  tff(c_412, plain, (![A_3, A_79, A_78]: (r1_tarski(A_3, k2_pre_topc(A_79, A_78)) | ~r1_tarski(A_3, A_78) | ~l1_pre_topc(A_79) | ~r1_tarski(A_78, u1_struct_0(A_79)))), inference(resolution, [status(thm)], [c_403, c_4])).
% 19.67/10.89  tff(c_14052, plain, (![A_3]: (r1_tarski(A_3, k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))) | ~r1_tarski(A_3, k2_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_14018, c_412])).
% 19.67/10.89  tff(c_14087, plain, (![A_3]: (r1_tarski(A_3, k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))) | ~r1_tarski(A_3, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_14052])).
% 19.67/10.89  tff(c_156, plain, (![A_55]: (r1_tarski(A_55, u1_struct_0('#skF_2')) | ~r1_tarski(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_75, c_146])).
% 19.67/10.89  tff(c_8836, plain, (![A_365, A_366]: (k2_xboole_0(A_365, k2_pre_topc(A_366, A_365))=k2_pre_topc(A_366, A_365) | ~l1_pre_topc(A_366) | ~r1_tarski(A_365, u1_struct_0(A_366)))), inference(resolution, [status(thm)], [c_403, c_2])).
% 19.67/10.89  tff(c_8846, plain, (![A_55]: (k2_xboole_0(A_55, k2_pre_topc('#skF_2', A_55))=k2_pre_topc('#skF_2', A_55) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_156, c_8836])).
% 19.67/10.89  tff(c_9042, plain, (![A_371]: (k2_xboole_0(A_371, k2_pre_topc('#skF_2', A_371))=k2_pre_topc('#skF_2', A_371) | ~r1_tarski(A_371, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8846])).
% 19.67/10.89  tff(c_9484, plain, (![A_371]: (r1_tarski(A_371, k2_pre_topc('#skF_2', A_371)) | ~r1_tarski(A_371, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9042, c_6])).
% 19.67/10.89  tff(c_10285, plain, (k2_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_10276])).
% 19.67/10.89  tff(c_10294, plain, (k2_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10285])).
% 19.67/10.89  tff(c_586, plain, (![A_6, A_88, B_89, B_7]: (r1_tarski(A_6, k2_xboole_0(A_88, B_89)) | ~r1_tarski(k2_xboole_0(A_6, B_7), A_88))), inference(resolution, [status(thm)], [c_6, c_550])).
% 19.67/10.89  tff(c_11402, plain, (![A_403, B_404]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), k2_xboole_0(A_403, B_404)) | ~r1_tarski(u1_struct_0('#skF_2'), A_403))), inference(superposition, [status(thm), theory('equality')], [c_10294, c_586])).
% 19.67/10.89  tff(c_11510, plain, (![A_405]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), A_405) | ~r1_tarski(u1_struct_0('#skF_2'), A_405))), inference(superposition, [status(thm), theory('equality')], [c_81, c_11402])).
% 19.67/10.89  tff(c_26659, plain, (![A_620, A_621]: (r1_tarski(A_620, A_621) | ~r1_tarski(A_620, k2_pre_topc('#skF_2', '#skF_3')) | ~r1_tarski(u1_struct_0('#skF_2'), A_621))), inference(resolution, [status(thm)], [c_11510, c_4])).
% 19.67/10.89  tff(c_26670, plain, (![A_621]: (r1_tarski('#skF_3', A_621) | ~r1_tarski(u1_struct_0('#skF_2'), A_621) | ~r1_tarski('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_9484, c_26659])).
% 19.67/10.89  tff(c_26701, plain, (![A_622]: (r1_tarski('#skF_3', A_622) | ~r1_tarski(u1_struct_0('#skF_2'), A_622))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26670])).
% 19.67/10.89  tff(c_26962, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))) | ~r1_tarski(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14087, c_26701])).
% 19.67/10.89  tff(c_27441, plain, (~r1_tarski(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_26962])).
% 19.67/10.89  tff(c_12012, plain, (v1_tops_1('#skF_1'('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_10812])).
% 19.67/10.89  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k2_pre_topc(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.67/10.89  tff(c_12197, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12011, c_16])).
% 19.67/10.89  tff(c_12235, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12197])).
% 19.67/10.89  tff(c_37777, plain, (~m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_12235])).
% 19.67/10.89  tff(c_37780, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_37777])).
% 19.67/10.89  tff(c_37787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_37780])).
% 19.67/10.89  tff(c_37789, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_12235])).
% 19.67/10.89  tff(c_103, plain, (![A_51]: (r1_tarski('#skF_1'(A_51), u1_struct_0(A_51)) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_99, c_12])).
% 19.67/10.89  tff(c_1333, plain, (![C_126, A_127, B_128]: (v1_tops_1(C_126, A_127) | ~r1_tarski(B_128, C_126) | ~v1_tops_1(B_128, A_127) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_94])).
% 19.67/10.89  tff(c_22346, plain, (![A_556, A_557]: (v1_tops_1(u1_struct_0(A_556), A_557) | ~v1_tops_1('#skF_1'(A_556), A_557) | ~m1_subset_1(u1_struct_0(A_556), k1_zfmisc_1(u1_struct_0(A_557))) | ~m1_subset_1('#skF_1'(A_556), k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557) | ~l1_pre_topc(A_556))), inference(resolution, [status(thm)], [c_103, c_1333])).
% 19.67/10.89  tff(c_54754, plain, (![A_952]: (v1_tops_1(u1_struct_0(A_952), A_952) | ~v1_tops_1('#skF_1'(A_952), A_952) | ~m1_subset_1('#skF_1'(A_952), k1_zfmisc_1(u1_struct_0(A_952))) | ~l1_pre_topc(A_952))), inference(resolution, [status(thm)], [c_45, c_22346])).
% 19.67/10.89  tff(c_54757, plain, (v1_tops_1(u1_struct_0('#skF_2'), '#skF_2') | ~v1_tops_1('#skF_1'('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_37789, c_54754])).
% 19.67/10.89  tff(c_54766, plain, (v1_tops_1(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_12012, c_54757])).
% 19.67/10.89  tff(c_721, plain, (![A_95]: (k2_pre_topc(A_95, u1_struct_0(A_95))=k2_struct_0(A_95) | ~v1_tops_1(u1_struct_0(A_95), A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_45, c_697])).
% 19.67/10.89  tff(c_54774, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54766, c_721])).
% 19.67/10.89  tff(c_54778, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54774])).
% 19.67/10.89  tff(c_8438, plain, (r1_tarski(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8252, c_6])).
% 19.67/10.89  tff(c_54831, plain, (r1_tarski(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54778, c_8438])).
% 19.67/10.89  tff(c_54861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27441, c_54831])).
% 19.67/10.89  tff(c_54863, plain, (r1_tarski(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_26962])).
% 19.67/10.89  tff(c_26692, plain, (![A_621]: (r1_tarski('#skF_3', A_621) | ~r1_tarski(u1_struct_0('#skF_2'), A_621))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26670])).
% 19.67/10.89  tff(c_54871, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54863, c_26692])).
% 19.67/10.89  tff(c_54929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19549, c_54871])).
% 19.67/10.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.67/10.89  
% 19.67/10.89  Inference rules
% 19.67/10.89  ----------------------
% 19.67/10.89  #Ref     : 0
% 19.67/10.89  #Sup     : 14100
% 19.67/10.89  #Fact    : 0
% 19.67/10.89  #Define  : 0
% 19.67/10.89  #Split   : 21
% 19.67/10.89  #Chain   : 0
% 19.67/10.89  #Close   : 0
% 19.67/10.89  
% 19.67/10.89  Ordering : KBO
% 19.67/10.89  
% 19.67/10.89  Simplification rules
% 19.67/10.89  ----------------------
% 19.67/10.89  #Subsume      : 3951
% 19.67/10.89  #Demod        : 4438
% 19.67/10.89  #Tautology    : 2327
% 19.67/10.89  #SimpNegUnit  : 61
% 19.67/10.89  #BackRed      : 69
% 19.67/10.89  
% 19.67/10.89  #Partial instantiations: 0
% 19.67/10.89  #Strategies tried      : 1
% 19.67/10.89  
% 19.67/10.89  Timing (in seconds)
% 19.67/10.89  ----------------------
% 19.67/10.90  Preprocessing        : 0.31
% 19.67/10.90  Parsing              : 0.17
% 19.67/10.90  CNF conversion       : 0.02
% 19.67/10.90  Main loop            : 9.72
% 19.67/10.90  Inferencing          : 1.29
% 19.67/10.90  Reduction            : 3.97
% 19.67/10.90  Demodulation         : 3.21
% 19.67/10.90  BG Simplification    : 0.16
% 19.67/10.90  Subsumption          : 3.72
% 19.67/10.90  Abstraction          : 0.22
% 19.67/10.90  MUC search           : 0.00
% 19.67/10.90  Cooper               : 0.00
% 19.67/10.90  Total                : 10.08
% 19.67/10.90  Index Insertion      : 0.00
% 19.67/10.90  Index Deletion       : 0.00
% 19.67/10.90  Index Matching       : 0.00
% 19.67/10.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
