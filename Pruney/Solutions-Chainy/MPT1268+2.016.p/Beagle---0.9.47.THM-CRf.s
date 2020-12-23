%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 153 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  198 ( 505 expanded)
%              Number of equality atoms :   27 (  64 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
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

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_155,plain,(
    ! [B_69,A_70] :
      ( v2_tops_1(B_69,A_70)
      | k1_tops_1(A_70,B_69) != k1_xboole_0
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_158,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_161,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_158])).

tff(c_162,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_161])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski('#skF_2'(A_85,B_86,C_87),C_87)
      | ~ r2_hidden(B_86,k1_tops_1(A_85,C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_211,plain,(
    ! [A_85,C_87,B_2] :
      ( r1_tarski('#skF_2'(A_85,'#skF_1'(k1_tops_1(A_85,C_87),B_2),C_87),C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | r1_tarski(k1_tops_1(A_85,C_87),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_115,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_1,B_2,B_59] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_59)
      | ~ r1_tarski(A_1,B_59)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_187,plain,(
    ! [A_78,B_79,C_80] :
      ( v3_pre_topc('#skF_2'(A_78,B_79,C_80),A_78)
      | ~ r2_hidden(B_79,k1_tops_1(A_78,C_80))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_189,plain,(
    ! [B_79] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_79,'#skF_4'),'#skF_3')
      | ~ r2_hidden(B_79,k1_tops_1('#skF_3','#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_187])).

tff(c_192,plain,(
    ! [B_79] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_79,'#skF_4'),'#skF_3')
      | ~ r2_hidden(B_79,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_189])).

tff(c_212,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1('#skF_2'(A_88,B_89,C_90),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ r2_hidden(B_89,k1_tops_1(A_88,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    ! [C_42] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_178,plain,(
    ! [C_42] :
      ( k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60])).

tff(c_218,plain,(
    ! [B_89,C_90] :
      ( '#skF_2'('#skF_3',B_89,C_90) = k1_xboole_0
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_89,C_90),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_3',B_89,C_90),'#skF_4')
      | ~ r2_hidden(B_89,k1_tops_1('#skF_3',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_212,c_178])).

tff(c_377,plain,(
    ! [B_122,C_123] :
      ( '#skF_2'('#skF_3',B_122,C_123) = k1_xboole_0
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_122,C_123),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_3',B_122,C_123),'#skF_4')
      | ~ r2_hidden(B_122,k1_tops_1('#skF_3',C_123))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_218])).

tff(c_379,plain,(
    ! [B_79] :
      ( '#skF_2'('#skF_3',B_79,'#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_2'('#skF_3',B_79,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(B_79,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_192,c_377])).

tff(c_383,plain,(
    ! [B_124] :
      ( '#skF_2'('#skF_3',B_124,'#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_2'('#skF_3',B_124,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_124,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_379])).

tff(c_394,plain,(
    ! [A_125,B_126] :
      ( '#skF_2'('#skF_3','#skF_1'(A_125,B_126),'#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_1'(A_125,B_126),'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_125,k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_118,c_383])).

tff(c_402,plain,(
    ! [B_2] :
      ( '#skF_2'('#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),'#skF_4') = k1_xboole_0
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(resolution,[status(thm)],[c_211,c_394])).

tff(c_408,plain,(
    ! [B_2] :
      ( '#skF_2'('#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),'#skF_4') = k1_xboole_0
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_12,c_402])).

tff(c_194,plain,(
    ! [B_82,A_83,C_84] :
      ( r2_hidden(B_82,'#skF_2'(A_83,B_82,C_84))
      | ~ r2_hidden(B_82,k1_tops_1(A_83,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_761,plain,(
    ! [A_146,C_147,B_148] :
      ( r2_hidden('#skF_1'(k1_tops_1(A_146,C_147),B_148),'#skF_2'(A_146,'#skF_1'(k1_tops_1(A_146,C_147),B_148),C_147))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | r1_tarski(k1_tops_1(A_146,C_147),B_148) ) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_771,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2)
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_761])).

tff(c_797,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_151),k1_xboole_0)
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_771])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_815,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_797,c_4])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_825,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_815,c_82])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_825])).

tff(c_834,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_835,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_837,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_44])).

tff(c_46,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_839,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_46])).

tff(c_48,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_849,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_48])).

tff(c_949,plain,(
    ! [A_178,B_179] :
      ( k1_tops_1(A_178,B_179) = k1_xboole_0
      | ~ v2_tops_1(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_955,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_949])).

tff(c_962,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_835,c_955])).

tff(c_1360,plain,(
    ! [B_247,A_248,C_249] :
      ( r1_tarski(B_247,k1_tops_1(A_248,C_249))
      | ~ r1_tarski(B_247,C_249)
      | ~ v3_pre_topc(B_247,A_248)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1366,plain,(
    ! [B_247] :
      ( r1_tarski(B_247,k1_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(B_247,'#skF_4')
      | ~ v3_pre_topc(B_247,'#skF_3')
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_1360])).

tff(c_1374,plain,(
    ! [B_250] :
      ( r1_tarski(B_250,k1_xboole_0)
      | ~ r1_tarski(B_250,'#skF_4')
      | ~ v3_pre_topc(B_250,'#skF_3')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_962,c_1366])).

tff(c_1381,plain,
    ( r1_tarski('#skF_5',k1_xboole_0)
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_849,c_1374])).

tff(c_1390,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_839,c_1381])).

tff(c_862,plain,(
    ! [B_160,A_161] :
      ( B_160 = A_161
      | ~ r1_tarski(B_160,A_161)
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_874,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_862])).

tff(c_1403,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1390,c_874])).

tff(c_1412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_1403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.59  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.58/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.58/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.59  
% 3.58/1.61  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.58/1.61  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.58/1.61  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.58/1.61  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 3.58/1.61  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.58/1.61  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.58/1.61  tff(c_42, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_64, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.58/1.61  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_155, plain, (![B_69, A_70]: (v2_tops_1(B_69, A_70) | k1_tops_1(A_70, B_69)!=k1_xboole_0 | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.58/1.61  tff(c_158, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_155])).
% 3.58/1.61  tff(c_161, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_158])).
% 3.58/1.61  tff(c_162, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_161])).
% 3.58/1.61  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.58/1.61  tff(c_203, plain, (![A_85, B_86, C_87]: (r1_tarski('#skF_2'(A_85, B_86, C_87), C_87) | ~r2_hidden(B_86, k1_tops_1(A_85, C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.61  tff(c_211, plain, (![A_85, C_87, B_2]: (r1_tarski('#skF_2'(A_85, '#skF_1'(k1_tops_1(A_85, C_87), B_2), C_87), C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | r1_tarski(k1_tops_1(A_85, C_87), B_2))), inference(resolution, [status(thm)], [c_6, c_203])).
% 3.58/1.61  tff(c_115, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.58/1.61  tff(c_118, plain, (![A_1, B_2, B_59]: (r2_hidden('#skF_1'(A_1, B_2), B_59) | ~r1_tarski(A_1, B_59) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_115])).
% 3.58/1.61  tff(c_187, plain, (![A_78, B_79, C_80]: (v3_pre_topc('#skF_2'(A_78, B_79, C_80), A_78) | ~r2_hidden(B_79, k1_tops_1(A_78, C_80)) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.61  tff(c_189, plain, (![B_79]: (v3_pre_topc('#skF_2'('#skF_3', B_79, '#skF_4'), '#skF_3') | ~r2_hidden(B_79, k1_tops_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_187])).
% 3.58/1.61  tff(c_192, plain, (![B_79]: (v3_pre_topc('#skF_2'('#skF_3', B_79, '#skF_4'), '#skF_3') | ~r2_hidden(B_79, k1_tops_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_189])).
% 3.58/1.61  tff(c_212, plain, (![A_88, B_89, C_90]: (m1_subset_1('#skF_2'(A_88, B_89, C_90), k1_zfmisc_1(u1_struct_0(A_88))) | ~r2_hidden(B_89, k1_tops_1(A_88, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.61  tff(c_60, plain, (![C_42]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_178, plain, (![C_42]: (k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_60])).
% 3.58/1.61  tff(c_218, plain, (![B_89, C_90]: ('#skF_2'('#skF_3', B_89, C_90)=k1_xboole_0 | ~v3_pre_topc('#skF_2'('#skF_3', B_89, C_90), '#skF_3') | ~r1_tarski('#skF_2'('#skF_3', B_89, C_90), '#skF_4') | ~r2_hidden(B_89, k1_tops_1('#skF_3', C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_212, c_178])).
% 3.58/1.61  tff(c_377, plain, (![B_122, C_123]: ('#skF_2'('#skF_3', B_122, C_123)=k1_xboole_0 | ~v3_pre_topc('#skF_2'('#skF_3', B_122, C_123), '#skF_3') | ~r1_tarski('#skF_2'('#skF_3', B_122, C_123), '#skF_4') | ~r2_hidden(B_122, k1_tops_1('#skF_3', C_123)) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_218])).
% 3.58/1.61  tff(c_379, plain, (![B_79]: ('#skF_2'('#skF_3', B_79, '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2'('#skF_3', B_79, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(B_79, k1_tops_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_192, c_377])).
% 3.58/1.61  tff(c_383, plain, (![B_124]: ('#skF_2'('#skF_3', B_124, '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2'('#skF_3', B_124, '#skF_4'), '#skF_4') | ~r2_hidden(B_124, k1_tops_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_379])).
% 3.58/1.61  tff(c_394, plain, (![A_125, B_126]: ('#skF_2'('#skF_3', '#skF_1'(A_125, B_126), '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2'('#skF_3', '#skF_1'(A_125, B_126), '#skF_4'), '#skF_4') | ~r1_tarski(A_125, k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(A_125, B_126))), inference(resolution, [status(thm)], [c_118, c_383])).
% 3.58/1.61  tff(c_402, plain, (![B_2]: ('#skF_2'('#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(resolution, [status(thm)], [c_211, c_394])).
% 3.58/1.61  tff(c_408, plain, (![B_2]: ('#skF_2'('#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), '#skF_4')=k1_xboole_0 | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_12, c_402])).
% 3.58/1.61  tff(c_194, plain, (![B_82, A_83, C_84]: (r2_hidden(B_82, '#skF_2'(A_83, B_82, C_84)) | ~r2_hidden(B_82, k1_tops_1(A_83, C_84)) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.61  tff(c_761, plain, (![A_146, C_147, B_148]: (r2_hidden('#skF_1'(k1_tops_1(A_146, C_147), B_148), '#skF_2'(A_146, '#skF_1'(k1_tops_1(A_146, C_147), B_148), C_147)) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | r1_tarski(k1_tops_1(A_146, C_147), B_148))), inference(resolution, [status(thm)], [c_6, c_194])).
% 3.58/1.61  tff(c_771, plain, (![B_2]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(superposition, [status(thm), theory('equality')], [c_408, c_761])).
% 3.58/1.61  tff(c_797, plain, (![B_151]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_151), k1_xboole_0) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_151))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_771])).
% 3.58/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.58/1.61  tff(c_815, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_797, c_4])).
% 3.58/1.61  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.58/1.61  tff(c_73, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.61  tff(c_82, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_73])).
% 3.58/1.61  tff(c_825, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_815, c_82])).
% 3.58/1.61  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_825])).
% 3.58/1.61  tff(c_834, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.58/1.61  tff(c_835, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.58/1.61  tff(c_44, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_837, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_44])).
% 3.58/1.61  tff(c_46, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_839, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_46])).
% 3.58/1.61  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.58/1.61  tff(c_849, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_48])).
% 3.58/1.61  tff(c_949, plain, (![A_178, B_179]: (k1_tops_1(A_178, B_179)=k1_xboole_0 | ~v2_tops_1(B_179, A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.58/1.61  tff(c_955, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_949])).
% 3.58/1.61  tff(c_962, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_835, c_955])).
% 3.58/1.61  tff(c_1360, plain, (![B_247, A_248, C_249]: (r1_tarski(B_247, k1_tops_1(A_248, C_249)) | ~r1_tarski(B_247, C_249) | ~v3_pre_topc(B_247, A_248) | ~m1_subset_1(C_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.58/1.61  tff(c_1366, plain, (![B_247]: (r1_tarski(B_247, k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(B_247, '#skF_4') | ~v3_pre_topc(B_247, '#skF_3') | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_1360])).
% 3.58/1.61  tff(c_1374, plain, (![B_250]: (r1_tarski(B_250, k1_xboole_0) | ~r1_tarski(B_250, '#skF_4') | ~v3_pre_topc(B_250, '#skF_3') | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_962, c_1366])).
% 3.58/1.61  tff(c_1381, plain, (r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_849, c_1374])).
% 3.58/1.61  tff(c_1390, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_837, c_839, c_1381])).
% 3.58/1.61  tff(c_862, plain, (![B_160, A_161]: (B_160=A_161 | ~r1_tarski(B_160, A_161) | ~r1_tarski(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.61  tff(c_874, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_862])).
% 3.58/1.61  tff(c_1403, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1390, c_874])).
% 3.58/1.61  tff(c_1412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_1403])).
% 3.58/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.61  
% 3.58/1.61  Inference rules
% 3.58/1.61  ----------------------
% 3.58/1.61  #Ref     : 0
% 3.58/1.61  #Sup     : 274
% 3.58/1.61  #Fact    : 0
% 3.58/1.61  #Define  : 0
% 3.58/1.61  #Split   : 9
% 3.58/1.61  #Chain   : 0
% 3.58/1.61  #Close   : 0
% 3.58/1.61  
% 3.58/1.61  Ordering : KBO
% 3.58/1.61  
% 3.58/1.61  Simplification rules
% 3.58/1.61  ----------------------
% 3.58/1.61  #Subsume      : 72
% 3.58/1.61  #Demod        : 176
% 3.58/1.61  #Tautology    : 56
% 3.58/1.61  #SimpNegUnit  : 10
% 3.58/1.61  #BackRed      : 0
% 3.58/1.61  
% 3.58/1.61  #Partial instantiations: 0
% 3.58/1.61  #Strategies tried      : 1
% 3.58/1.61  
% 3.58/1.61  Timing (in seconds)
% 3.58/1.61  ----------------------
% 3.58/1.61  Preprocessing        : 0.32
% 3.58/1.61  Parsing              : 0.16
% 3.58/1.61  CNF conversion       : 0.02
% 3.58/1.61  Main loop            : 0.53
% 3.58/1.62  Inferencing          : 0.18
% 3.58/1.62  Reduction            : 0.15
% 3.58/1.62  Demodulation         : 0.10
% 3.58/1.62  BG Simplification    : 0.02
% 3.58/1.62  Subsumption          : 0.13
% 3.58/1.62  Abstraction          : 0.02
% 3.58/1.62  MUC search           : 0.00
% 3.58/1.62  Cooper               : 0.00
% 3.58/1.62  Total                : 0.88
% 3.58/1.62  Index Insertion      : 0.00
% 3.58/1.62  Index Deletion       : 0.00
% 3.58/1.62  Index Matching       : 0.00
% 3.58/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
