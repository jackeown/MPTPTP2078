%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 307 expanded)
%              Number of leaves         :   27 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 ( 974 expanded)
%              Number of equality atoms :   46 ( 128 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_39,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1422,plain,(
    ! [A_150,B_151] :
      ( r1_tarski(k1_tops_1(A_150,B_151),B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1430,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1422])).

tff(c_1435,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1430])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1537,plain,(
    ! [A_157,B_158] :
      ( v3_pre_topc(k1_tops_1(A_157,B_158),A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1545,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1537])).

tff(c_1550,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1545])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_1367,plain,(
    ! [A_141,C_142,B_143] :
      ( r1_tarski(A_141,C_142)
      | ~ r1_tarski(B_143,C_142)
      | ~ r1_tarski(A_141,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1388,plain,(
    ! [A_146] :
      ( r1_tarski(A_146,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_77,c_1367])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1393,plain,(
    ! [A_3,A_146] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_146)
      | ~ r1_tarski(A_146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1388,c_8])).

tff(c_1437,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1435,c_1393])).

tff(c_1444,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1437])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tops_1(A_52,B_53),B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_156,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_163,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_156])).

tff(c_1151,plain,(
    ! [A_125,B_126] :
      ( v3_pre_topc(k1_tops_1(A_125,B_126),A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1156,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1151])).

tff(c_1163,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1156])).

tff(c_108,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_77,c_108])).

tff(c_134,plain,(
    ! [A_3,A_49] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_49)
      | ~ r1_tarski(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_129,c_8])).

tff(c_166,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_134])).

tff(c_173,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_772,plain,(
    ! [B_99,A_100] :
      ( v2_tops_1(B_99,A_100)
      | k1_tops_1(A_100,B_99) != k1_xboole_0
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_779,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_772])).

tff(c_787,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_779])).

tff(c_788,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_787])).

tff(c_44,plain,(
    ! [C_32] :
      ( k1_xboole_0 != '#skF_3'
      | k1_xboole_0 = C_32
      | ~ v3_pre_topc(C_32,'#skF_1')
      | ~ r1_tarski(C_32,'#skF_2')
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_48,plain,(
    ! [C_32] :
      ( r1_tarski('#skF_3','#skF_2')
      | k1_xboole_0 = C_32
      | ~ v3_pre_topc(C_32,'#skF_1')
      | ~ r1_tarski(C_32,'#skF_2')
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_282,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [C_32] :
      ( v3_pre_topc('#skF_3','#skF_1')
      | k1_xboole_0 = C_32
      | ~ v3_pre_topc(C_32,'#skF_1')
      | ~ r1_tarski(C_32,'#skF_2')
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_207,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_284,plain,
    ( r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_134])).

tff(c_291,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_284])).

tff(c_52,plain,(
    ! [C_32] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_32
      | ~ v3_pre_topc(C_32,'#skF_1')
      | ~ r1_tarski(C_32,'#skF_2')
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_336,plain,(
    ! [C_64] :
      ( k1_xboole_0 = C_64
      | ~ v3_pre_topc(C_64,'#skF_1')
      | ~ r1_tarski(C_64,'#skF_2')
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52])).

tff(c_570,plain,(
    ! [A_84] :
      ( k1_xboole_0 = A_84
      | ~ v3_pre_topc(A_84,'#skF_1')
      | ~ r1_tarski(A_84,'#skF_2')
      | ~ r1_tarski(A_84,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_336])).

tff(c_576,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_291,c_570])).

tff(c_601,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_207,c_576])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_601])).

tff(c_657,plain,(
    ! [C_89] :
      ( k1_xboole_0 = C_89
      | ~ v3_pre_topc(C_89,'#skF_1')
      | ~ r1_tarski(C_89,'#skF_2')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_791,plain,(
    ! [A_102] :
      ( k1_xboole_0 = A_102
      | ~ v3_pre_topc(A_102,'#skF_1')
      | ~ r1_tarski(A_102,'#skF_2')
      | ~ r1_tarski(A_102,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_657])).

tff(c_802,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_173,c_791])).

tff(c_821,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_802])).

tff(c_822,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_821])).

tff(c_887,plain,(
    ! [A_108,B_109] :
      ( v3_pre_topc(k1_tops_1(A_108,B_109),A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_892,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_887])).

tff(c_899,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_892])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_899])).

tff(c_957,plain,(
    ! [C_112] :
      ( k1_xboole_0 = C_112
      | ~ v3_pre_topc(C_112,'#skF_1')
      | ~ r1_tarski(C_112,'#skF_2')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1171,plain,(
    ! [A_128] :
      ( k1_xboole_0 = A_128
      | ~ v3_pre_topc(A_128,'#skF_1')
      | ~ r1_tarski(A_128,'#skF_2')
      | ~ r1_tarski(A_128,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_957])).

tff(c_1184,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_173,c_1171])).

tff(c_1207,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1163,c_1184])).

tff(c_1286,plain,(
    ! [B_134,A_135] :
      ( v2_tops_1(B_134,A_135)
      | k1_tops_1(A_135,B_134) != k1_xboole_0
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1293,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1286])).

tff(c_1301,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1207,c_1293])).

tff(c_1303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1301])).

tff(c_1305,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1325,plain,(
    ! [C_32] :
      ( v2_tops_1('#skF_2','#skF_1')
      | C_32 = '#skF_3'
      | ~ v3_pre_topc(C_32,'#skF_1')
      | ~ r1_tarski(C_32,'#skF_2')
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_52])).

tff(c_1327,plain,(
    ! [C_138] :
      ( C_138 = '#skF_3'
      | ~ v3_pre_topc(C_138,'#skF_1')
      | ~ r1_tarski(C_138,'#skF_2')
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1325])).

tff(c_1709,plain,(
    ! [A_174] :
      ( A_174 = '#skF_3'
      | ~ v3_pre_topc(A_174,'#skF_1')
      | ~ r1_tarski(A_174,'#skF_2')
      | ~ r1_tarski(A_174,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1327])).

tff(c_1720,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_3'
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1444,c_1709])).

tff(c_1739,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_1550,c_1720])).

tff(c_24,plain,(
    ! [B_24,A_22] :
      ( v2_tops_1(B_24,A_22)
      | k1_tops_1(A_22,B_24) != k1_xboole_0
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1802,plain,(
    ! [B_178,A_179] :
      ( v2_tops_1(B_178,A_179)
      | k1_tops_1(A_179,B_178) != '#skF_3'
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_24])).

tff(c_1813,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1802])).

tff(c_1818,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1739,c_1813])).

tff(c_1820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1818])).

tff(c_1821,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1822,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1826,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_36])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1824,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_38])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1873,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_40])).

tff(c_2131,plain,(
    ! [A_206,B_207] :
      ( k1_tops_1(A_206,B_207) = k1_xboole_0
      | ~ v2_tops_1(B_207,A_206)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2141,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2131])).

tff(c_2152,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1822,c_2141])).

tff(c_2441,plain,(
    ! [B_228,A_229,C_230] :
      ( r1_tarski(B_228,k1_tops_1(A_229,C_230))
      | ~ r1_tarski(B_228,C_230)
      | ~ v3_pre_topc(B_228,A_229)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2448,plain,(
    ! [B_228] :
      ( r1_tarski(B_228,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_228,'#skF_2')
      | ~ v3_pre_topc(B_228,'#skF_1')
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_2441])).

tff(c_2545,plain,(
    ! [B_235] :
      ( r1_tarski(B_235,k1_xboole_0)
      | ~ r1_tarski(B_235,'#skF_2')
      | ~ v3_pre_topc(B_235,'#skF_1')
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2152,c_2448])).

tff(c_2548,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1873,c_2545])).

tff(c_2562,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_1824,c_2548])).

tff(c_10,plain,(
    ! [A_6] : k1_subset_1(A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_1828,plain,(
    ! [A_182,B_183] :
      ( r1_tarski(A_182,B_183)
      | ~ m1_subset_1(A_182,k1_zfmisc_1(B_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1840,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_53,c_1828])).

tff(c_1842,plain,(
    ! [B_185,A_186] :
      ( B_185 = A_186
      | ~ r1_tarski(B_185,A_186)
      | ~ r1_tarski(A_186,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1852,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1840,c_1842])).

tff(c_2582,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2562,c_1852])).

tff(c_2599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1821,c_2582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  
% 4.13/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.13/1.75  
% 4.13/1.75  %Foreground sorts:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Background operators:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Foreground operators:
% 4.13/1.75  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.75  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.13/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.13/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.75  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.13/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.75  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.13/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.13/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.13/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.75  
% 4.51/1.77  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.51/1.77  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.51/1.77  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.51/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.77  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.51/1.77  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.51/1.77  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.51/1.77  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.51/1.77  tff(f_39, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.51/1.77  tff(f_41, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 4.51/1.77  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_64, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 4.51/1.77  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_1422, plain, (![A_150, B_151]: (r1_tarski(k1_tops_1(A_150, B_151), B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.51/1.77  tff(c_1430, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1422])).
% 4.51/1.77  tff(c_1435, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1430])).
% 4.51/1.77  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_1537, plain, (![A_157, B_158]: (v3_pre_topc(k1_tops_1(A_157, B_158), A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.51/1.77  tff(c_1545, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1537])).
% 4.51/1.77  tff(c_1550, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1545])).
% 4.51/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.77  tff(c_66, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.77  tff(c_77, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_66])).
% 4.51/1.77  tff(c_1367, plain, (![A_141, C_142, B_143]: (r1_tarski(A_141, C_142) | ~r1_tarski(B_143, C_142) | ~r1_tarski(A_141, B_143))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.51/1.77  tff(c_1388, plain, (![A_146]: (r1_tarski(A_146, u1_struct_0('#skF_1')) | ~r1_tarski(A_146, '#skF_2'))), inference(resolution, [status(thm)], [c_77, c_1367])).
% 4.51/1.77  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.51/1.77  tff(c_1393, plain, (![A_3, A_146]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_146) | ~r1_tarski(A_146, '#skF_2'))), inference(resolution, [status(thm)], [c_1388, c_8])).
% 4.51/1.77  tff(c_1437, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1435, c_1393])).
% 4.51/1.77  tff(c_1444, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1437])).
% 4.51/1.77  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.77  tff(c_151, plain, (![A_52, B_53]: (r1_tarski(k1_tops_1(A_52, B_53), B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.51/1.77  tff(c_156, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_151])).
% 4.51/1.77  tff(c_163, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_156])).
% 4.51/1.77  tff(c_1151, plain, (![A_125, B_126]: (v3_pre_topc(k1_tops_1(A_125, B_126), A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.51/1.77  tff(c_1156, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1151])).
% 4.51/1.77  tff(c_1163, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1156])).
% 4.51/1.77  tff(c_108, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.51/1.77  tff(c_129, plain, (![A_49]: (r1_tarski(A_49, u1_struct_0('#skF_1')) | ~r1_tarski(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_77, c_108])).
% 4.51/1.77  tff(c_134, plain, (![A_3, A_49]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_49) | ~r1_tarski(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_129, c_8])).
% 4.51/1.77  tff(c_166, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_163, c_134])).
% 4.51/1.77  tff(c_173, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_166])).
% 4.51/1.77  tff(c_772, plain, (![B_99, A_100]: (v2_tops_1(B_99, A_100) | k1_tops_1(A_100, B_99)!=k1_xboole_0 | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.77  tff(c_779, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_772])).
% 4.51/1.77  tff(c_787, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_779])).
% 4.51/1.77  tff(c_788, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_787])).
% 4.51/1.77  tff(c_44, plain, (![C_32]: (k1_xboole_0!='#skF_3' | k1_xboole_0=C_32 | ~v3_pre_topc(C_32, '#skF_1') | ~r1_tarski(C_32, '#skF_2') | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_107, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 4.51/1.77  tff(c_48, plain, (![C_32]: (r1_tarski('#skF_3', '#skF_2') | k1_xboole_0=C_32 | ~v3_pre_topc(C_32, '#skF_1') | ~r1_tarski(C_32, '#skF_2') | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_282, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.51/1.77  tff(c_46, plain, (![C_32]: (v3_pre_topc('#skF_3', '#skF_1') | k1_xboole_0=C_32 | ~v3_pre_topc(C_32, '#skF_1') | ~r1_tarski(C_32, '#skF_2') | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_207, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.51/1.77  tff(c_284, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_282, c_134])).
% 4.51/1.77  tff(c_291, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_284])).
% 4.51/1.77  tff(c_52, plain, (![C_32]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_32 | ~v3_pre_topc(C_32, '#skF_1') | ~r1_tarski(C_32, '#skF_2') | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_336, plain, (![C_64]: (k1_xboole_0=C_64 | ~v3_pre_topc(C_64, '#skF_1') | ~r1_tarski(C_64, '#skF_2') | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_52])).
% 4.51/1.77  tff(c_570, plain, (![A_84]: (k1_xboole_0=A_84 | ~v3_pre_topc(A_84, '#skF_1') | ~r1_tarski(A_84, '#skF_2') | ~r1_tarski(A_84, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_336])).
% 4.51/1.77  tff(c_576, plain, (k1_xboole_0='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_291, c_570])).
% 4.51/1.77  tff(c_601, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_207, c_576])).
% 4.51/1.77  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_601])).
% 4.51/1.77  tff(c_657, plain, (![C_89]: (k1_xboole_0=C_89 | ~v3_pre_topc(C_89, '#skF_1') | ~r1_tarski(C_89, '#skF_2') | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_48])).
% 4.51/1.77  tff(c_791, plain, (![A_102]: (k1_xboole_0=A_102 | ~v3_pre_topc(A_102, '#skF_1') | ~r1_tarski(A_102, '#skF_2') | ~r1_tarski(A_102, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_657])).
% 4.51/1.77  tff(c_802, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_173, c_791])).
% 4.51/1.77  tff(c_821, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_802])).
% 4.51/1.77  tff(c_822, plain, (~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_788, c_821])).
% 4.51/1.77  tff(c_887, plain, (![A_108, B_109]: (v3_pre_topc(k1_tops_1(A_108, B_109), A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.51/1.77  tff(c_892, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_887])).
% 4.51/1.77  tff(c_899, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_892])).
% 4.51/1.77  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_822, c_899])).
% 4.51/1.77  tff(c_957, plain, (![C_112]: (k1_xboole_0=C_112 | ~v3_pre_topc(C_112, '#skF_1') | ~r1_tarski(C_112, '#skF_2') | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 4.51/1.77  tff(c_1171, plain, (![A_128]: (k1_xboole_0=A_128 | ~v3_pre_topc(A_128, '#skF_1') | ~r1_tarski(A_128, '#skF_2') | ~r1_tarski(A_128, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_957])).
% 4.51/1.77  tff(c_1184, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_173, c_1171])).
% 4.51/1.77  tff(c_1207, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1163, c_1184])).
% 4.51/1.77  tff(c_1286, plain, (![B_134, A_135]: (v2_tops_1(B_134, A_135) | k1_tops_1(A_135, B_134)!=k1_xboole_0 | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.77  tff(c_1293, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1286])).
% 4.51/1.77  tff(c_1301, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1207, c_1293])).
% 4.51/1.77  tff(c_1303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1301])).
% 4.51/1.77  tff(c_1305, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 4.51/1.77  tff(c_1325, plain, (![C_32]: (v2_tops_1('#skF_2', '#skF_1') | C_32='#skF_3' | ~v3_pre_topc(C_32, '#skF_1') | ~r1_tarski(C_32, '#skF_2') | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_52])).
% 4.51/1.77  tff(c_1327, plain, (![C_138]: (C_138='#skF_3' | ~v3_pre_topc(C_138, '#skF_1') | ~r1_tarski(C_138, '#skF_2') | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1325])).
% 4.51/1.77  tff(c_1709, plain, (![A_174]: (A_174='#skF_3' | ~v3_pre_topc(A_174, '#skF_1') | ~r1_tarski(A_174, '#skF_2') | ~r1_tarski(A_174, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_1327])).
% 4.51/1.77  tff(c_1720, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_3' | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1444, c_1709])).
% 4.51/1.77  tff(c_1739, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_1550, c_1720])).
% 4.51/1.77  tff(c_24, plain, (![B_24, A_22]: (v2_tops_1(B_24, A_22) | k1_tops_1(A_22, B_24)!=k1_xboole_0 | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.77  tff(c_1802, plain, (![B_178, A_179]: (v2_tops_1(B_178, A_179) | k1_tops_1(A_179, B_178)!='#skF_3' | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_24])).
% 4.51/1.77  tff(c_1813, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1802])).
% 4.51/1.77  tff(c_1818, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1739, c_1813])).
% 4.51/1.77  tff(c_1820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1818])).
% 4.51/1.77  tff(c_1821, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 4.51/1.77  tff(c_1822, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 4.51/1.77  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_1826, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_36])).
% 4.51/1.77  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_1824, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_38])).
% 4.51/1.77  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.77  tff(c_1873, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_40])).
% 4.51/1.77  tff(c_2131, plain, (![A_206, B_207]: (k1_tops_1(A_206, B_207)=k1_xboole_0 | ~v2_tops_1(B_207, A_206) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.77  tff(c_2141, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2131])).
% 4.51/1.77  tff(c_2152, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1822, c_2141])).
% 4.51/1.77  tff(c_2441, plain, (![B_228, A_229, C_230]: (r1_tarski(B_228, k1_tops_1(A_229, C_230)) | ~r1_tarski(B_228, C_230) | ~v3_pre_topc(B_228, A_229) | ~m1_subset_1(C_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.51/1.77  tff(c_2448, plain, (![B_228]: (r1_tarski(B_228, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_228, '#skF_2') | ~v3_pre_topc(B_228, '#skF_1') | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_2441])).
% 4.51/1.77  tff(c_2545, plain, (![B_235]: (r1_tarski(B_235, k1_xboole_0) | ~r1_tarski(B_235, '#skF_2') | ~v3_pre_topc(B_235, '#skF_1') | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2152, c_2448])).
% 4.51/1.77  tff(c_2548, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1873, c_2545])).
% 4.51/1.77  tff(c_2562, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1826, c_1824, c_2548])).
% 4.51/1.77  tff(c_10, plain, (![A_6]: (k1_subset_1(A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.77  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.77  tff(c_53, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 4.51/1.77  tff(c_1828, plain, (![A_182, B_183]: (r1_tarski(A_182, B_183) | ~m1_subset_1(A_182, k1_zfmisc_1(B_183)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.51/1.77  tff(c_1840, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_53, c_1828])).
% 4.51/1.77  tff(c_1842, plain, (![B_185, A_186]: (B_185=A_186 | ~r1_tarski(B_185, A_186) | ~r1_tarski(A_186, B_185))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.77  tff(c_1852, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_1840, c_1842])).
% 4.51/1.77  tff(c_2582, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2562, c_1852])).
% 4.51/1.77  tff(c_2599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1821, c_2582])).
% 4.51/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.77  
% 4.51/1.77  Inference rules
% 4.51/1.77  ----------------------
% 4.51/1.77  #Ref     : 0
% 4.51/1.77  #Sup     : 527
% 4.51/1.77  #Fact    : 0
% 4.51/1.77  #Define  : 0
% 4.51/1.77  #Split   : 23
% 4.51/1.77  #Chain   : 0
% 4.51/1.77  #Close   : 0
% 4.51/1.77  
% 4.51/1.77  Ordering : KBO
% 4.51/1.77  
% 4.51/1.77  Simplification rules
% 4.51/1.77  ----------------------
% 4.51/1.77  #Subsume      : 237
% 4.51/1.77  #Demod        : 318
% 4.51/1.77  #Tautology    : 130
% 4.51/1.77  #SimpNegUnit  : 16
% 4.51/1.77  #BackRed      : 18
% 4.51/1.77  
% 4.51/1.77  #Partial instantiations: 0
% 4.51/1.77  #Strategies tried      : 1
% 4.51/1.77  
% 4.51/1.77  Timing (in seconds)
% 4.51/1.77  ----------------------
% 4.51/1.78  Preprocessing        : 0.32
% 4.51/1.78  Parsing              : 0.17
% 4.51/1.78  CNF conversion       : 0.02
% 4.51/1.78  Main loop            : 0.67
% 4.51/1.78  Inferencing          : 0.23
% 4.51/1.78  Reduction            : 0.22
% 4.51/1.78  Demodulation         : 0.15
% 4.51/1.78  BG Simplification    : 0.02
% 4.51/1.78  Subsumption          : 0.15
% 4.51/1.78  Abstraction          : 0.03
% 4.51/1.78  MUC search           : 0.00
% 4.51/1.78  Cooper               : 0.00
% 4.51/1.78  Total                : 1.04
% 4.51/1.78  Index Insertion      : 0.00
% 4.51/1.78  Index Deletion       : 0.00
% 4.51/1.78  Index Matching       : 0.00
% 4.51/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
