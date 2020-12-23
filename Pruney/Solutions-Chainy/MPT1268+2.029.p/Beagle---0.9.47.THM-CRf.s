%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:50 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 351 expanded)
%              Number of leaves         :   27 ( 126 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 (1090 expanded)
%              Number of equality atoms :   50 ( 144 expanded)
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

tff(f_104,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_76,axiom,(
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

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1412,plain,(
    ! [B_141,A_142] :
      ( v2_tops_1(B_141,A_142)
      | k1_tops_1(A_142,B_141) != k1_xboole_0
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1419,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1412])).

tff(c_1423,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1419])).

tff(c_1424,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1423])).

tff(c_159,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_168,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_164])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1509,plain,(
    ! [A_153,B_154] :
      ( v3_pre_topc(k1_tops_1(A_153,B_154),A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1514,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1509])).

tff(c_1518,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1514])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_121,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_53,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_121])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [A_7,A_53] :
      ( r1_tarski(A_7,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_7,A_53)
      | ~ r1_tarski(A_53,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_134,c_12])).

tff(c_170,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_168,c_139])).

tff(c_177,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_940,plain,(
    ! [B_105,A_106] :
      ( v2_tops_1(B_105,A_106)
      | k1_tops_1(A_106,B_105) != k1_xboole_0
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_947,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_940])).

tff(c_951,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_947])).

tff(c_952,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_951])).

tff(c_242,plain,(
    ! [A_60,B_61] :
      ( v3_pre_topc(k1_tops_1(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_247,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_242])).

tff(c_251,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_247])).

tff(c_44,plain,(
    ! [C_34] :
      ( k1_xboole_0 != '#skF_3'
      | k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_120,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_48,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_3','#skF_2')
      | k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_203,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [C_34] :
      ( v3_pre_topc('#skF_3','#skF_1')
      | k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_262,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_205,plain,
    ( r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_203,c_139])).

tff(c_212,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_205])).

tff(c_52,plain,(
    ! [C_34] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_356,plain,(
    ! [C_69] :
      ( k1_xboole_0 = C_69
      | ~ v3_pre_topc(C_69,'#skF_1')
      | ~ r1_tarski(C_69,'#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52])).

tff(c_720,plain,(
    ! [A_95] :
      ( k1_xboole_0 = A_95
      | ~ v3_pre_topc(A_95,'#skF_1')
      | ~ r1_tarski(A_95,'#skF_2')
      | ~ r1_tarski(A_95,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_356])).

tff(c_726,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_720])).

tff(c_747,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_262,c_726])).

tff(c_749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_747])).

tff(c_779,plain,(
    ! [C_97] :
      ( k1_xboole_0 = C_97
      | ~ v3_pre_topc(C_97,'#skF_1')
      | ~ r1_tarski(C_97,'#skF_2')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1200,plain,(
    ! [A_125] :
      ( k1_xboole_0 = A_125
      | ~ v3_pre_topc(A_125,'#skF_1')
      | ~ r1_tarski(A_125,'#skF_2')
      | ~ r1_tarski(A_125,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_779])).

tff(c_1209,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_1200])).

tff(c_1231,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_251,c_1209])).

tff(c_1233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_952,c_1231])).

tff(c_1266,plain,(
    ! [C_128] :
      ( k1_xboole_0 = C_128
      | ~ v3_pre_topc(C_128,'#skF_1')
      | ~ r1_tarski(C_128,'#skF_2')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1616,plain,(
    ! [A_169] :
      ( k1_xboole_0 = A_169
      | ~ v3_pre_topc(A_169,'#skF_1')
      | ~ r1_tarski(A_169,'#skF_2')
      | ~ r1_tarski(A_169,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1266])).

tff(c_1627,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_1616])).

tff(c_1646,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1518,c_1627])).

tff(c_1648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1424,c_1646])).

tff(c_1650,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [B_26,A_24] :
      ( v2_tops_1(B_26,A_24)
      | k1_tops_1(A_24,B_26) != k1_xboole_0
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2089,plain,(
    ! [B_213,A_214] :
      ( v2_tops_1(B_213,A_214)
      | k1_tops_1(A_214,B_213) != '#skF_3'
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_24])).

tff(c_2096,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2089])).

tff(c_2100,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2096])).

tff(c_2101,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2100])).

tff(c_1771,plain,(
    ! [A_186,B_187] :
      ( r1_tarski(k1_tops_1(A_186,B_187),B_187)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1776,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1771])).

tff(c_1780,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1776])).

tff(c_1688,plain,(
    ! [A_173,C_174,B_175] :
      ( r1_tarski(A_173,C_174)
      | ~ r1_tarski(B_175,C_174)
      | ~ r1_tarski(A_173,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1713,plain,(
    ! [A_178] :
      ( r1_tarski(A_178,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_178,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_1688])).

tff(c_1718,plain,(
    ! [A_7,A_178] :
      ( r1_tarski(A_7,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_7,A_178)
      | ~ r1_tarski(A_178,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1713,c_12])).

tff(c_1784,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1780,c_1718])).

tff(c_1792,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1784])).

tff(c_1649,plain,(
    ! [C_34] :
      ( k1_xboole_0 = C_34
      | ~ v3_pre_topc(C_34,'#skF_1')
      | ~ r1_tarski(C_34,'#skF_2')
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1852,plain,(
    ! [C_192] :
      ( C_192 = '#skF_3'
      | ~ v3_pre_topc(C_192,'#skF_1')
      | ~ r1_tarski(C_192,'#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1649])).

tff(c_2108,plain,(
    ! [A_218] :
      ( A_218 = '#skF_3'
      | ~ v3_pre_topc(A_218,'#skF_1')
      | ~ r1_tarski(A_218,'#skF_2')
      | ~ r1_tarski(A_218,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1852])).

tff(c_2119,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_3'
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1792,c_2108])).

tff(c_2138,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_3'
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_2119])).

tff(c_2139,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2101,c_2138])).

tff(c_2190,plain,(
    ! [A_225,B_226] :
      ( v3_pre_topc(k1_tops_1(A_225,B_226),A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2195,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2190])).

tff(c_2199,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2195])).

tff(c_2201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2139,c_2199])).

tff(c_2202,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2203,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_40,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2245,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_40])).

tff(c_2406,plain,(
    ! [A_250,B_251] :
      ( r1_tarski(k1_tops_1(A_250,B_251),B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2408,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2245,c_2406])).

tff(c_2416,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2408])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2276,plain,(
    ! [A_240,C_241,B_242] :
      ( r1_tarski(A_240,C_241)
      | ~ r1_tarski(B_242,C_241)
      | ~ r1_tarski(A_240,B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2839,plain,(
    ! [A_275,C_276,B_277,A_278] :
      ( r1_tarski(A_275,k2_xboole_0(C_276,B_277))
      | ~ r1_tarski(A_275,A_278)
      | ~ r1_tarski(A_278,B_277) ) ),
    inference(resolution,[status(thm)],[c_8,c_2276])).

tff(c_3096,plain,(
    ! [C_294,B_295] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k2_xboole_0(C_294,B_295))
      | ~ r1_tarski('#skF_3',B_295) ) ),
    inference(resolution,[status(thm)],[c_2416,c_2839])).

tff(c_3111,plain,(
    ! [A_6] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),A_6)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3096])).

tff(c_3121,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3111])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2207,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_36])).

tff(c_38,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2205,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_38])).

tff(c_2591,plain,(
    ! [A_260,B_261] :
      ( k1_tops_1(A_260,B_261) = k1_xboole_0
      | ~ v2_tops_1(B_261,A_260)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2601,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2591])).

tff(c_2609,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2203,c_2601])).

tff(c_2883,plain,(
    ! [B_279,A_280,C_281] :
      ( r1_tarski(B_279,k1_tops_1(A_280,C_281))
      | ~ r1_tarski(B_279,C_281)
      | ~ v3_pre_topc(B_279,A_280)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2890,plain,(
    ! [B_279] :
      ( r1_tarski(B_279,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_279,'#skF_2')
      | ~ v3_pre_topc(B_279,'#skF_1')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_2883])).

tff(c_3262,plain,(
    ! [B_307] :
      ( r1_tarski(B_307,k1_xboole_0)
      | ~ r1_tarski(B_307,'#skF_2')
      | ~ v3_pre_topc(B_307,'#skF_1')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2609,c_2890])).

tff(c_3265,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_2245,c_3262])).

tff(c_3275,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2205,c_3265])).

tff(c_3277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3121,c_3275])).

tff(c_3279,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3111])).

tff(c_2218,plain,(
    ! [A_231,C_232,B_233] :
      ( r1_tarski(A_231,k2_xboole_0(C_232,B_233))
      | ~ r1_tarski(A_231,B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2239,plain,(
    ! [A_236,A_237] :
      ( r1_tarski(A_236,A_237)
      | ~ r1_tarski(A_236,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2218])).

tff(c_2250,plain,(
    ! [A_238] : r1_tarski(k1_xboole_0,A_238) ),
    inference(resolution,[status(thm)],[c_6,c_2239])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2258,plain,(
    ! [A_238] :
      ( k1_xboole_0 = A_238
      | ~ r1_tarski(A_238,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2250,c_2])).

tff(c_3292,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3279,c_2258])).

tff(c_3313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2202,c_3292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.79  
% 4.65/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.79  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.65/1.79  
% 4.65/1.79  %Foreground sorts:
% 4.65/1.79  
% 4.65/1.79  
% 4.65/1.79  %Background operators:
% 4.65/1.79  
% 4.65/1.79  
% 4.65/1.79  %Foreground operators:
% 4.65/1.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.65/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.79  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.65/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.65/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.65/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.65/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.65/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.65/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.65/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.79  
% 4.65/1.81  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.65/1.81  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.65/1.81  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.65/1.81  tff(f_55, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.65/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.65/1.81  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.65/1.81  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.65/1.81  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.65/1.81  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.65/1.81  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.65/1.81  tff(c_34, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_64, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 4.65/1.81  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_1412, plain, (![B_141, A_142]: (v2_tops_1(B_141, A_142) | k1_tops_1(A_142, B_141)!=k1_xboole_0 | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.65/1.81  tff(c_1419, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1412])).
% 4.65/1.81  tff(c_1423, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1419])).
% 4.65/1.81  tff(c_1424, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_1423])).
% 4.65/1.81  tff(c_159, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.81  tff(c_164, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_159])).
% 4.65/1.81  tff(c_168, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_164])).
% 4.65/1.81  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_1509, plain, (![A_153, B_154]: (v3_pre_topc(k1_tops_1(A_153, B_154), A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.65/1.81  tff(c_1514, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1509])).
% 4.65/1.81  tff(c_1518, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1514])).
% 4.65/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.81  tff(c_66, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.65/1.81  tff(c_74, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_66])).
% 4.65/1.81  tff(c_121, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.81  tff(c_134, plain, (![A_53]: (r1_tarski(A_53, u1_struct_0('#skF_1')) | ~r1_tarski(A_53, '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_121])).
% 4.65/1.81  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.81  tff(c_139, plain, (![A_7, A_53]: (r1_tarski(A_7, u1_struct_0('#skF_1')) | ~r1_tarski(A_7, A_53) | ~r1_tarski(A_53, '#skF_2'))), inference(resolution, [status(thm)], [c_134, c_12])).
% 4.65/1.81  tff(c_170, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_168, c_139])).
% 4.65/1.81  tff(c_177, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_170])).
% 4.65/1.81  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.65/1.81  tff(c_940, plain, (![B_105, A_106]: (v2_tops_1(B_105, A_106) | k1_tops_1(A_106, B_105)!=k1_xboole_0 | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.65/1.81  tff(c_947, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_940])).
% 4.65/1.81  tff(c_951, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_947])).
% 4.65/1.81  tff(c_952, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_951])).
% 4.65/1.81  tff(c_242, plain, (![A_60, B_61]: (v3_pre_topc(k1_tops_1(A_60, B_61), A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.65/1.81  tff(c_247, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_242])).
% 4.65/1.81  tff(c_251, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_247])).
% 4.65/1.81  tff(c_44, plain, (![C_34]: (k1_xboole_0!='#skF_3' | k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_120, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 4.65/1.81  tff(c_48, plain, (![C_34]: (r1_tarski('#skF_3', '#skF_2') | k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_203, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.65/1.81  tff(c_46, plain, (![C_34]: (v3_pre_topc('#skF_3', '#skF_1') | k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_262, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 4.65/1.81  tff(c_205, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_203, c_139])).
% 4.65/1.81  tff(c_212, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_205])).
% 4.65/1.81  tff(c_52, plain, (![C_34]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_356, plain, (![C_69]: (k1_xboole_0=C_69 | ~v3_pre_topc(C_69, '#skF_1') | ~r1_tarski(C_69, '#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_52])).
% 4.65/1.81  tff(c_720, plain, (![A_95]: (k1_xboole_0=A_95 | ~v3_pre_topc(A_95, '#skF_1') | ~r1_tarski(A_95, '#skF_2') | ~r1_tarski(A_95, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_356])).
% 4.65/1.81  tff(c_726, plain, (k1_xboole_0='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_212, c_720])).
% 4.65/1.81  tff(c_747, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_262, c_726])).
% 4.65/1.81  tff(c_749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_747])).
% 4.65/1.81  tff(c_779, plain, (![C_97]: (k1_xboole_0=C_97 | ~v3_pre_topc(C_97, '#skF_1') | ~r1_tarski(C_97, '#skF_2') | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 4.65/1.81  tff(c_1200, plain, (![A_125]: (k1_xboole_0=A_125 | ~v3_pre_topc(A_125, '#skF_1') | ~r1_tarski(A_125, '#skF_2') | ~r1_tarski(A_125, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_779])).
% 4.65/1.81  tff(c_1209, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_177, c_1200])).
% 4.65/1.81  tff(c_1231, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_168, c_251, c_1209])).
% 4.65/1.81  tff(c_1233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_952, c_1231])).
% 4.65/1.81  tff(c_1266, plain, (![C_128]: (k1_xboole_0=C_128 | ~v3_pre_topc(C_128, '#skF_1') | ~r1_tarski(C_128, '#skF_2') | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_48])).
% 4.65/1.81  tff(c_1616, plain, (![A_169]: (k1_xboole_0=A_169 | ~v3_pre_topc(A_169, '#skF_1') | ~r1_tarski(A_169, '#skF_2') | ~r1_tarski(A_169, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_1266])).
% 4.65/1.81  tff(c_1627, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_177, c_1616])).
% 4.65/1.81  tff(c_1646, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_168, c_1518, c_1627])).
% 4.65/1.81  tff(c_1648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1424, c_1646])).
% 4.65/1.81  tff(c_1650, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.81  tff(c_24, plain, (![B_26, A_24]: (v2_tops_1(B_26, A_24) | k1_tops_1(A_24, B_26)!=k1_xboole_0 | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.65/1.81  tff(c_2089, plain, (![B_213, A_214]: (v2_tops_1(B_213, A_214) | k1_tops_1(A_214, B_213)!='#skF_3' | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_24])).
% 4.65/1.81  tff(c_2096, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2089])).
% 4.65/1.81  tff(c_2100, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2096])).
% 4.65/1.81  tff(c_2101, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_64, c_2100])).
% 4.65/1.81  tff(c_1771, plain, (![A_186, B_187]: (r1_tarski(k1_tops_1(A_186, B_187), B_187) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.81  tff(c_1776, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1771])).
% 4.65/1.81  tff(c_1780, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1776])).
% 4.65/1.81  tff(c_1688, plain, (![A_173, C_174, B_175]: (r1_tarski(A_173, C_174) | ~r1_tarski(B_175, C_174) | ~r1_tarski(A_173, B_175))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.81  tff(c_1713, plain, (![A_178]: (r1_tarski(A_178, u1_struct_0('#skF_1')) | ~r1_tarski(A_178, '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_1688])).
% 4.65/1.81  tff(c_1718, plain, (![A_7, A_178]: (r1_tarski(A_7, u1_struct_0('#skF_1')) | ~r1_tarski(A_7, A_178) | ~r1_tarski(A_178, '#skF_2'))), inference(resolution, [status(thm)], [c_1713, c_12])).
% 4.65/1.81  tff(c_1784, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1780, c_1718])).
% 4.65/1.81  tff(c_1792, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1784])).
% 4.65/1.81  tff(c_1649, plain, (![C_34]: (k1_xboole_0=C_34 | ~v3_pre_topc(C_34, '#skF_1') | ~r1_tarski(C_34, '#skF_2') | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.81  tff(c_1852, plain, (![C_192]: (C_192='#skF_3' | ~v3_pre_topc(C_192, '#skF_1') | ~r1_tarski(C_192, '#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1649])).
% 4.65/1.81  tff(c_2108, plain, (![A_218]: (A_218='#skF_3' | ~v3_pre_topc(A_218, '#skF_1') | ~r1_tarski(A_218, '#skF_2') | ~r1_tarski(A_218, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_1852])).
% 4.65/1.81  tff(c_2119, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_3' | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1792, c_2108])).
% 4.65/1.81  tff(c_2138, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_3' | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_2119])).
% 4.65/1.81  tff(c_2139, plain, (~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2101, c_2138])).
% 4.65/1.81  tff(c_2190, plain, (![A_225, B_226]: (v3_pre_topc(k1_tops_1(A_225, B_226), A_225) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.65/1.81  tff(c_2195, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2190])).
% 4.65/1.81  tff(c_2199, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2195])).
% 4.65/1.81  tff(c_2201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2139, c_2199])).
% 4.65/1.81  tff(c_2202, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 4.65/1.81  tff(c_10, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.81  tff(c_2203, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 4.65/1.81  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_2245, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_40])).
% 4.65/1.81  tff(c_2406, plain, (![A_250, B_251]: (r1_tarski(k1_tops_1(A_250, B_251), B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.65/1.81  tff(c_2408, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2245, c_2406])).
% 4.65/1.81  tff(c_2416, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2408])).
% 4.65/1.81  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.65/1.81  tff(c_2276, plain, (![A_240, C_241, B_242]: (r1_tarski(A_240, C_241) | ~r1_tarski(B_242, C_241) | ~r1_tarski(A_240, B_242))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.81  tff(c_2839, plain, (![A_275, C_276, B_277, A_278]: (r1_tarski(A_275, k2_xboole_0(C_276, B_277)) | ~r1_tarski(A_275, A_278) | ~r1_tarski(A_278, B_277))), inference(resolution, [status(thm)], [c_8, c_2276])).
% 4.65/1.81  tff(c_3096, plain, (![C_294, B_295]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k2_xboole_0(C_294, B_295)) | ~r1_tarski('#skF_3', B_295))), inference(resolution, [status(thm)], [c_2416, c_2839])).
% 4.65/1.81  tff(c_3111, plain, (![A_6]: (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), A_6) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3096])).
% 4.65/1.81  tff(c_3121, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3111])).
% 4.65/1.81  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_2207, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_36])).
% 4.65/1.81  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.65/1.81  tff(c_2205, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_38])).
% 4.65/1.81  tff(c_2591, plain, (![A_260, B_261]: (k1_tops_1(A_260, B_261)=k1_xboole_0 | ~v2_tops_1(B_261, A_260) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.65/1.81  tff(c_2601, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2591])).
% 4.65/1.81  tff(c_2609, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2203, c_2601])).
% 4.65/1.81  tff(c_2883, plain, (![B_279, A_280, C_281]: (r1_tarski(B_279, k1_tops_1(A_280, C_281)) | ~r1_tarski(B_279, C_281) | ~v3_pre_topc(B_279, A_280) | ~m1_subset_1(C_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.65/1.81  tff(c_2890, plain, (![B_279]: (r1_tarski(B_279, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_279, '#skF_2') | ~v3_pre_topc(B_279, '#skF_1') | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_2883])).
% 4.65/1.81  tff(c_3262, plain, (![B_307]: (r1_tarski(B_307, k1_xboole_0) | ~r1_tarski(B_307, '#skF_2') | ~v3_pre_topc(B_307, '#skF_1') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2609, c_2890])).
% 4.65/1.81  tff(c_3265, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_2245, c_3262])).
% 4.65/1.81  tff(c_3275, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2205, c_3265])).
% 4.65/1.81  tff(c_3277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3121, c_3275])).
% 4.65/1.81  tff(c_3279, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3111])).
% 4.65/1.81  tff(c_2218, plain, (![A_231, C_232, B_233]: (r1_tarski(A_231, k2_xboole_0(C_232, B_233)) | ~r1_tarski(A_231, B_233))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.65/1.81  tff(c_2239, plain, (![A_236, A_237]: (r1_tarski(A_236, A_237) | ~r1_tarski(A_236, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2218])).
% 4.65/1.81  tff(c_2250, plain, (![A_238]: (r1_tarski(k1_xboole_0, A_238))), inference(resolution, [status(thm)], [c_6, c_2239])).
% 4.65/1.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.81  tff(c_2258, plain, (![A_238]: (k1_xboole_0=A_238 | ~r1_tarski(A_238, k1_xboole_0))), inference(resolution, [status(thm)], [c_2250, c_2])).
% 4.65/1.81  tff(c_3292, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3279, c_2258])).
% 4.65/1.81  tff(c_3313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2202, c_3292])).
% 4.65/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.81  
% 4.65/1.81  Inference rules
% 4.65/1.81  ----------------------
% 4.65/1.81  #Ref     : 0
% 4.65/1.81  #Sup     : 764
% 4.65/1.81  #Fact    : 0
% 4.65/1.81  #Define  : 0
% 4.65/1.81  #Split   : 32
% 4.65/1.81  #Chain   : 0
% 4.65/1.81  #Close   : 0
% 4.65/1.81  
% 4.65/1.81  Ordering : KBO
% 4.65/1.81  
% 4.65/1.81  Simplification rules
% 4.65/1.81  ----------------------
% 4.65/1.81  #Subsume      : 273
% 4.65/1.81  #Demod        : 275
% 4.65/1.81  #Tautology    : 143
% 4.65/1.81  #SimpNegUnit  : 19
% 4.65/1.81  #BackRed      : 7
% 4.65/1.81  
% 4.65/1.81  #Partial instantiations: 0
% 4.65/1.81  #Strategies tried      : 1
% 4.65/1.81  
% 4.65/1.81  Timing (in seconds)
% 4.65/1.81  ----------------------
% 4.84/1.82  Preprocessing        : 0.30
% 4.84/1.82  Parsing              : 0.16
% 4.84/1.82  CNF conversion       : 0.02
% 4.84/1.82  Main loop            : 0.74
% 4.84/1.82  Inferencing          : 0.23
% 4.84/1.82  Reduction            : 0.24
% 4.84/1.82  Demodulation         : 0.16
% 4.84/1.82  BG Simplification    : 0.03
% 4.84/1.82  Subsumption          : 0.19
% 4.84/1.82  Abstraction          : 0.03
% 4.84/1.82  MUC search           : 0.00
% 4.84/1.82  Cooper               : 0.00
% 4.84/1.82  Total                : 1.09
% 4.84/1.82  Index Insertion      : 0.00
% 4.84/1.82  Index Deletion       : 0.00
% 4.84/1.82  Index Matching       : 0.00
% 4.84/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
