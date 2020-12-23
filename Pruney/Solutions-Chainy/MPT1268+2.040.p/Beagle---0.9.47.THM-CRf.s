%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:52 EST 2020

% Result     : Theorem 16.19s
% Output     : CNFRefutation 16.19s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 225 expanded)
%              Number of leaves         :   38 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  257 ( 677 expanded)
%              Number of equality atoms :   32 (  83 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_151,negated_conjecture,(
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

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_123,axiom,(
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

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_81,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12881,plain,(
    ! [B_462,A_463] :
      ( v2_tops_1(B_462,A_463)
      | k1_tops_1(A_463,B_462) != k1_xboole_0
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0(A_463)))
      | ~ l1_pre_topc(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12888,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_12881])).

tff(c_12900,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12888])).

tff(c_12901,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_12900])).

tff(c_12236,plain,(
    ! [A_430,B_431] :
      ( r1_tarski(k1_tops_1(A_430,B_431),B_431)
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ l1_pre_topc(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12241,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_12236])).

tff(c_12251,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12241])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_13022,plain,(
    ! [A_470,B_471] :
      ( k1_tops_1(A_470,k1_tops_1(A_470,B_471)) = k1_tops_1(A_470,B_471)
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_pre_topc(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_13030,plain,
    ( k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_13022])).

tff(c_13041,plain,(
    k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13030])).

tff(c_180,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),A_93)
      | r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_188,plain,(
    ! [A_93] : r1_tarski(A_93,A_93) ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_101,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_219,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_tarski(A_101,C_102)
      | ~ r1_tarski(B_103,C_102)
      | ~ r1_tarski(A_101,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12203,plain,(
    ! [A_428] :
      ( r1_tarski(A_428,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_428,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_115,c_219])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13172,plain,(
    ! [A_475,A_476] :
      ( r1_tarski(A_475,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_475,A_476)
      | ~ r1_tarski(A_476,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12203,c_12])).

tff(c_13194,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_12251,c_13172])).

tff(c_13233,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_13194])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [C_56,A_44,D_58,B_52] :
      ( v3_pre_topc(C_56,A_44)
      | k1_tops_1(A_44,C_56) != C_56
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(B_52)))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(B_52)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15211,plain,(
    ! [D_549,B_550] :
      ( ~ m1_subset_1(D_549,k1_zfmisc_1(u1_struct_0(B_550)))
      | ~ l1_pre_topc(B_550) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_15222,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_15211])).

tff(c_15234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_15222])).

tff(c_15542,plain,(
    ! [C_557,A_558] :
      ( v3_pre_topc(C_557,A_558)
      | k1_tops_1(A_558,C_557) != C_557
      | ~ m1_subset_1(C_557,k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_24810,plain,(
    ! [A_731,A_732] :
      ( v3_pre_topc(A_731,A_732)
      | k1_tops_1(A_732,A_731) != A_731
      | ~ l1_pre_topc(A_732)
      | ~ v2_pre_topc(A_732)
      | ~ r1_tarski(A_731,u1_struct_0(A_732)) ) ),
    inference(resolution,[status(thm)],[c_26,c_15542])).

tff(c_24989,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_4')) != k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_13233,c_24810])).

tff(c_25128,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_13041,c_24989])).

tff(c_233,plain,(
    ! [A_101] :
      ( r1_tarski(A_101,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_101,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_115,c_219])).

tff(c_78,plain,(
    ! [C_69] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_69
      | ~ v3_pre_topc(C_69,'#skF_3')
      | ~ r1_tarski(C_69,'#skF_4')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12176,plain,(
    ! [C_426] :
      ( k1_xboole_0 = C_426
      | ~ v3_pre_topc(C_426,'#skF_3')
      | ~ r1_tarski(C_426,'#skF_4')
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_78])).

tff(c_12635,plain,(
    ! [A_456] :
      ( k1_xboole_0 = A_456
      | ~ v3_pre_topc(A_456,'#skF_3')
      | ~ r1_tarski(A_456,'#skF_4')
      | ~ r1_tarski(A_456,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_12176])).

tff(c_12691,plain,(
    ! [A_101] :
      ( k1_xboole_0 = A_101
      | ~ v3_pre_topc(A_101,'#skF_3')
      | ~ r1_tarski(A_101,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_233,c_12635])).

tff(c_25154,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_25128,c_12691])).

tff(c_25160,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12251,c_25154])).

tff(c_25162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12901,c_25160])).

tff(c_25163,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_25164,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_25177,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25164,c_62])).

tff(c_64,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_25175,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25164,c_64])).

tff(c_66,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_25213,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25164,c_66])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25596,plain,(
    ! [A_785,B_786] :
      ( r1_tarski(k1_tops_1(A_785,B_786),B_786)
      | ~ m1_subset_1(B_786,k1_zfmisc_1(u1_struct_0(A_785)))
      | ~ l1_pre_topc(A_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_25633,plain,(
    ! [A_787] :
      ( r1_tarski(k1_tops_1(A_787,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_787) ) ),
    inference(resolution,[status(thm)],[c_20,c_25596])).

tff(c_16,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25647,plain,(
    ! [A_788] :
      ( k1_tops_1(A_788,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_788) ) ),
    inference(resolution,[status(thm)],[c_25633,c_16])).

tff(c_25651,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_25647])).

tff(c_26138,plain,(
    ! [A_808,B_809,C_810] :
      ( r1_tarski('#skF_2'(A_808,B_809,C_810),C_810)
      | ~ r2_hidden(B_809,k1_tops_1(A_808,C_810))
      | ~ m1_subset_1(C_810,k1_zfmisc_1(u1_struct_0(A_808)))
      | ~ l1_pre_topc(A_808)
      | ~ v2_pre_topc(A_808) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26144,plain,(
    ! [B_809] :
      ( r1_tarski('#skF_2'('#skF_3',B_809,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_809,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25651,c_26138])).

tff(c_26271,plain,(
    ! [B_815] :
      ( r1_tarski('#skF_2'('#skF_3',B_815,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_815,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_20,c_26144])).

tff(c_14,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25311,plain,(
    ! [A_762,C_763,B_764] :
      ( r1_tarski(A_762,C_763)
      | ~ r1_tarski(B_764,C_763)
      | ~ r1_tarski(A_762,B_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25332,plain,(
    ! [A_762,A_14] :
      ( r1_tarski(A_762,A_14)
      | ~ r1_tarski(A_762,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_25311])).

tff(c_26985,plain,(
    ! [B_857,A_858] :
      ( r1_tarski('#skF_2'('#skF_3',B_857,k1_xboole_0),A_858)
      | ~ r2_hidden(B_857,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26271,c_25332])).

tff(c_26487,plain,(
    ! [B_824,A_825,C_826] :
      ( r2_hidden(B_824,'#skF_2'(A_825,B_824,C_826))
      | ~ r2_hidden(B_824,k1_tops_1(A_825,C_826))
      | ~ m1_subset_1(C_826,k1_zfmisc_1(u1_struct_0(A_825)))
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26493,plain,(
    ! [B_824] :
      ( r2_hidden(B_824,'#skF_2'('#skF_3',B_824,k1_xboole_0))
      | ~ r2_hidden(B_824,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25651,c_26487])).

tff(c_26510,plain,(
    ! [B_831] :
      ( r2_hidden(B_831,'#skF_2'('#skF_3',B_831,k1_xboole_0))
      | ~ r2_hidden(B_831,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_20,c_26493])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26520,plain,(
    ! [B_831] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_831,k1_xboole_0),B_831)
      | ~ r2_hidden(B_831,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26510,c_30])).

tff(c_27049,plain,(
    ! [A_858] : ~ r2_hidden(A_858,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26985,c_26520])).

tff(c_25817,plain,(
    ! [A_798,B_799] :
      ( k1_tops_1(A_798,B_799) = k1_xboole_0
      | ~ v2_tops_1(B_799,A_798)
      | ~ m1_subset_1(B_799,k1_zfmisc_1(u1_struct_0(A_798)))
      | ~ l1_pre_topc(A_798) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_25831,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_25817])).

tff(c_25844,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_25164,c_25831])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27469,plain,(
    ! [B_874,A_875,C_876,D_877] :
      ( r2_hidden(B_874,k1_tops_1(A_875,C_876))
      | ~ r2_hidden(B_874,D_877)
      | ~ r1_tarski(D_877,C_876)
      | ~ v3_pre_topc(D_877,A_875)
      | ~ m1_subset_1(D_877,k1_zfmisc_1(u1_struct_0(A_875)))
      | ~ m1_subset_1(C_876,k1_zfmisc_1(u1_struct_0(A_875)))
      | ~ l1_pre_topc(A_875)
      | ~ v2_pre_topc(A_875) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44896,plain,(
    ! [A_1206,B_1207,A_1208,C_1209] :
      ( r2_hidden('#skF_1'(A_1206,B_1207),k1_tops_1(A_1208,C_1209))
      | ~ r1_tarski(A_1206,C_1209)
      | ~ v3_pre_topc(A_1206,A_1208)
      | ~ m1_subset_1(A_1206,k1_zfmisc_1(u1_struct_0(A_1208)))
      | ~ m1_subset_1(C_1209,k1_zfmisc_1(u1_struct_0(A_1208)))
      | ~ l1_pre_topc(A_1208)
      | ~ v2_pre_topc(A_1208)
      | r1_tarski(A_1206,B_1207) ) ),
    inference(resolution,[status(thm)],[c_6,c_27469])).

tff(c_44937,plain,(
    ! [A_1206,B_1207] :
      ( r2_hidden('#skF_1'(A_1206,B_1207),k1_xboole_0)
      | ~ r1_tarski(A_1206,'#skF_4')
      | ~ v3_pre_topc(A_1206,'#skF_3')
      | ~ m1_subset_1(A_1206,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(A_1206,B_1207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25844,c_44896])).

tff(c_44959,plain,(
    ! [A_1206,B_1207] :
      ( r2_hidden('#skF_1'(A_1206,B_1207),k1_xboole_0)
      | ~ r1_tarski(A_1206,'#skF_4')
      | ~ v3_pre_topc(A_1206,'#skF_3')
      | ~ m1_subset_1(A_1206,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_1206,B_1207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_44937])).

tff(c_61268,plain,(
    ! [A_1438,B_1439] :
      ( ~ r1_tarski(A_1438,'#skF_4')
      | ~ v3_pre_topc(A_1438,'#skF_3')
      | ~ m1_subset_1(A_1438,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_1438,B_1439) ) ),
    inference(negUnitSimplification,[status(thm)],[c_27049,c_44959])).

tff(c_61279,plain,(
    ! [B_1439] :
      ( ~ r1_tarski('#skF_5','#skF_4')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | r1_tarski('#skF_5',B_1439) ) ),
    inference(resolution,[status(thm)],[c_25213,c_61268])).

tff(c_61314,plain,(
    ! [B_1440] : r1_tarski('#skF_5',B_1440) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25177,c_25175,c_61279])).

tff(c_61559,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_61314,c_16])).

tff(c_61683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25163,c_61559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.19/9.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.19/9.12  
% 16.19/9.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.19/9.12  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 16.19/9.12  
% 16.19/9.12  %Foreground sorts:
% 16.19/9.12  
% 16.19/9.12  
% 16.19/9.12  %Background operators:
% 16.19/9.12  
% 16.19/9.12  
% 16.19/9.12  %Foreground operators:
% 16.19/9.12  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.19/9.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.19/9.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.19/9.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.19/9.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.19/9.12  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 16.19/9.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.19/9.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.19/9.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.19/9.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.19/9.12  tff('#skF_5', type, '#skF_5': $i).
% 16.19/9.12  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.19/9.12  tff('#skF_3', type, '#skF_3': $i).
% 16.19/9.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.19/9.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.19/9.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.19/9.12  tff('#skF_4', type, '#skF_4': $i).
% 16.19/9.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.19/9.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.19/9.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.19/9.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.19/9.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.19/9.12  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 16.19/9.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.19/9.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.19/9.12  
% 16.19/9.14  tff(f_151, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 16.19/9.14  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 16.19/9.14  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 16.19/9.14  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 16.19/9.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.19/9.14  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.19/9.14  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.19/9.14  tff(f_123, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 16.19/9.14  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 16.19/9.14  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 16.19/9.14  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 16.19/9.14  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.19/9.14  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.19/9.14  tff(c_60, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_81, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 16.19/9.14  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_12881, plain, (![B_462, A_463]: (v2_tops_1(B_462, A_463) | k1_tops_1(A_463, B_462)!=k1_xboole_0 | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0(A_463))) | ~l1_pre_topc(A_463))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.19/9.14  tff(c_12888, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_12881])).
% 16.19/9.14  tff(c_12900, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12888])).
% 16.19/9.14  tff(c_12901, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_81, c_12900])).
% 16.19/9.14  tff(c_12236, plain, (![A_430, B_431]: (r1_tarski(k1_tops_1(A_430, B_431), B_431) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_430))) | ~l1_pre_topc(A_430))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.19/9.14  tff(c_12241, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_12236])).
% 16.19/9.14  tff(c_12251, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12241])).
% 16.19/9.14  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_13022, plain, (![A_470, B_471]: (k1_tops_1(A_470, k1_tops_1(A_470, B_471))=k1_tops_1(A_470, B_471) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_pre_topc(A_470))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.19/9.14  tff(c_13030, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_13022])).
% 16.19/9.14  tff(c_13041, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_13030])).
% 16.19/9.14  tff(c_180, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), A_93) | r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.19/9.14  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.19/9.14  tff(c_188, plain, (![A_93]: (r1_tarski(A_93, A_93))), inference(resolution, [status(thm)], [c_180, c_4])).
% 16.19/9.14  tff(c_101, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.19/9.14  tff(c_115, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_101])).
% 16.19/9.14  tff(c_219, plain, (![A_101, C_102, B_103]: (r1_tarski(A_101, C_102) | ~r1_tarski(B_103, C_102) | ~r1_tarski(A_101, B_103))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.19/9.14  tff(c_12203, plain, (![A_428]: (r1_tarski(A_428, u1_struct_0('#skF_3')) | ~r1_tarski(A_428, '#skF_4'))), inference(resolution, [status(thm)], [c_115, c_219])).
% 16.19/9.14  tff(c_12, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.19/9.14  tff(c_13172, plain, (![A_475, A_476]: (r1_tarski(A_475, u1_struct_0('#skF_3')) | ~r1_tarski(A_475, A_476) | ~r1_tarski(A_476, '#skF_4'))), inference(resolution, [status(thm)], [c_12203, c_12])).
% 16.19/9.14  tff(c_13194, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_12251, c_13172])).
% 16.19/9.14  tff(c_13233, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_13194])).
% 16.19/9.14  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.19/9.14  tff(c_46, plain, (![C_56, A_44, D_58, B_52]: (v3_pre_topc(C_56, A_44) | k1_tops_1(A_44, C_56)!=C_56 | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0(B_52))) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(B_52) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_123])).
% 16.19/9.14  tff(c_15211, plain, (![D_549, B_550]: (~m1_subset_1(D_549, k1_zfmisc_1(u1_struct_0(B_550))) | ~l1_pre_topc(B_550))), inference(splitLeft, [status(thm)], [c_46])).
% 16.19/9.14  tff(c_15222, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_15211])).
% 16.19/9.14  tff(c_15234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_15222])).
% 16.19/9.14  tff(c_15542, plain, (![C_557, A_558]: (v3_pre_topc(C_557, A_558) | k1_tops_1(A_558, C_557)!=C_557 | ~m1_subset_1(C_557, k1_zfmisc_1(u1_struct_0(A_558))) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558))), inference(splitRight, [status(thm)], [c_46])).
% 16.19/9.14  tff(c_24810, plain, (![A_731, A_732]: (v3_pre_topc(A_731, A_732) | k1_tops_1(A_732, A_731)!=A_731 | ~l1_pre_topc(A_732) | ~v2_pre_topc(A_732) | ~r1_tarski(A_731, u1_struct_0(A_732)))), inference(resolution, [status(thm)], [c_26, c_15542])).
% 16.19/9.14  tff(c_24989, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_4'))!=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_13233, c_24810])).
% 16.19/9.14  tff(c_25128, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_13041, c_24989])).
% 16.19/9.14  tff(c_233, plain, (![A_101]: (r1_tarski(A_101, u1_struct_0('#skF_3')) | ~r1_tarski(A_101, '#skF_4'))), inference(resolution, [status(thm)], [c_115, c_219])).
% 16.19/9.14  tff(c_78, plain, (![C_69]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_69 | ~v3_pre_topc(C_69, '#skF_3') | ~r1_tarski(C_69, '#skF_4') | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_12176, plain, (![C_426]: (k1_xboole_0=C_426 | ~v3_pre_topc(C_426, '#skF_3') | ~r1_tarski(C_426, '#skF_4') | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_81, c_78])).
% 16.19/9.14  tff(c_12635, plain, (![A_456]: (k1_xboole_0=A_456 | ~v3_pre_topc(A_456, '#skF_3') | ~r1_tarski(A_456, '#skF_4') | ~r1_tarski(A_456, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_26, c_12176])).
% 16.19/9.14  tff(c_12691, plain, (![A_101]: (k1_xboole_0=A_101 | ~v3_pre_topc(A_101, '#skF_3') | ~r1_tarski(A_101, '#skF_4'))), inference(resolution, [status(thm)], [c_233, c_12635])).
% 16.19/9.14  tff(c_25154, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_25128, c_12691])).
% 16.19/9.14  tff(c_25160, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12251, c_25154])).
% 16.19/9.14  tff(c_25162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12901, c_25160])).
% 16.19/9.14  tff(c_25163, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 16.19/9.14  tff(c_25164, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 16.19/9.14  tff(c_62, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_25177, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25164, c_62])).
% 16.19/9.14  tff(c_64, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_25175, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25164, c_64])).
% 16.19/9.14  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/9.14  tff(c_25213, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_25164, c_66])).
% 16.19/9.14  tff(c_20, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.19/9.14  tff(c_25596, plain, (![A_785, B_786]: (r1_tarski(k1_tops_1(A_785, B_786), B_786) | ~m1_subset_1(B_786, k1_zfmisc_1(u1_struct_0(A_785))) | ~l1_pre_topc(A_785))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.19/9.14  tff(c_25633, plain, (![A_787]: (r1_tarski(k1_tops_1(A_787, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_787))), inference(resolution, [status(thm)], [c_20, c_25596])).
% 16.19/9.14  tff(c_16, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.19/9.14  tff(c_25647, plain, (![A_788]: (k1_tops_1(A_788, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_788))), inference(resolution, [status(thm)], [c_25633, c_16])).
% 16.19/9.14  tff(c_25651, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_25647])).
% 16.19/9.14  tff(c_26138, plain, (![A_808, B_809, C_810]: (r1_tarski('#skF_2'(A_808, B_809, C_810), C_810) | ~r2_hidden(B_809, k1_tops_1(A_808, C_810)) | ~m1_subset_1(C_810, k1_zfmisc_1(u1_struct_0(A_808))) | ~l1_pre_topc(A_808) | ~v2_pre_topc(A_808))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.19/9.14  tff(c_26144, plain, (![B_809]: (r1_tarski('#skF_2'('#skF_3', B_809, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_809, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25651, c_26138])).
% 16.19/9.14  tff(c_26271, plain, (![B_815]: (r1_tarski('#skF_2'('#skF_3', B_815, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_815, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_20, c_26144])).
% 16.19/9.14  tff(c_14, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.19/9.14  tff(c_25311, plain, (![A_762, C_763, B_764]: (r1_tarski(A_762, C_763) | ~r1_tarski(B_764, C_763) | ~r1_tarski(A_762, B_764))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.19/9.14  tff(c_25332, plain, (![A_762, A_14]: (r1_tarski(A_762, A_14) | ~r1_tarski(A_762, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_25311])).
% 16.19/9.14  tff(c_26985, plain, (![B_857, A_858]: (r1_tarski('#skF_2'('#skF_3', B_857, k1_xboole_0), A_858) | ~r2_hidden(B_857, k1_xboole_0))), inference(resolution, [status(thm)], [c_26271, c_25332])).
% 16.19/9.14  tff(c_26487, plain, (![B_824, A_825, C_826]: (r2_hidden(B_824, '#skF_2'(A_825, B_824, C_826)) | ~r2_hidden(B_824, k1_tops_1(A_825, C_826)) | ~m1_subset_1(C_826, k1_zfmisc_1(u1_struct_0(A_825))) | ~l1_pre_topc(A_825) | ~v2_pre_topc(A_825))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.19/9.14  tff(c_26493, plain, (![B_824]: (r2_hidden(B_824, '#skF_2'('#skF_3', B_824, k1_xboole_0)) | ~r2_hidden(B_824, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25651, c_26487])).
% 16.19/9.14  tff(c_26510, plain, (![B_831]: (r2_hidden(B_831, '#skF_2'('#skF_3', B_831, k1_xboole_0)) | ~r2_hidden(B_831, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_20, c_26493])).
% 16.19/9.14  tff(c_30, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.19/9.14  tff(c_26520, plain, (![B_831]: (~r1_tarski('#skF_2'('#skF_3', B_831, k1_xboole_0), B_831) | ~r2_hidden(B_831, k1_xboole_0))), inference(resolution, [status(thm)], [c_26510, c_30])).
% 16.19/9.14  tff(c_27049, plain, (![A_858]: (~r2_hidden(A_858, k1_xboole_0))), inference(resolution, [status(thm)], [c_26985, c_26520])).
% 16.19/9.14  tff(c_25817, plain, (![A_798, B_799]: (k1_tops_1(A_798, B_799)=k1_xboole_0 | ~v2_tops_1(B_799, A_798) | ~m1_subset_1(B_799, k1_zfmisc_1(u1_struct_0(A_798))) | ~l1_pre_topc(A_798))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.19/9.14  tff(c_25831, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_25817])).
% 16.19/9.14  tff(c_25844, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_25164, c_25831])).
% 16.19/9.14  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.19/9.14  tff(c_27469, plain, (![B_874, A_875, C_876, D_877]: (r2_hidden(B_874, k1_tops_1(A_875, C_876)) | ~r2_hidden(B_874, D_877) | ~r1_tarski(D_877, C_876) | ~v3_pre_topc(D_877, A_875) | ~m1_subset_1(D_877, k1_zfmisc_1(u1_struct_0(A_875))) | ~m1_subset_1(C_876, k1_zfmisc_1(u1_struct_0(A_875))) | ~l1_pre_topc(A_875) | ~v2_pre_topc(A_875))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.19/9.14  tff(c_44896, plain, (![A_1206, B_1207, A_1208, C_1209]: (r2_hidden('#skF_1'(A_1206, B_1207), k1_tops_1(A_1208, C_1209)) | ~r1_tarski(A_1206, C_1209) | ~v3_pre_topc(A_1206, A_1208) | ~m1_subset_1(A_1206, k1_zfmisc_1(u1_struct_0(A_1208))) | ~m1_subset_1(C_1209, k1_zfmisc_1(u1_struct_0(A_1208))) | ~l1_pre_topc(A_1208) | ~v2_pre_topc(A_1208) | r1_tarski(A_1206, B_1207))), inference(resolution, [status(thm)], [c_6, c_27469])).
% 16.19/9.14  tff(c_44937, plain, (![A_1206, B_1207]: (r2_hidden('#skF_1'(A_1206, B_1207), k1_xboole_0) | ~r1_tarski(A_1206, '#skF_4') | ~v3_pre_topc(A_1206, '#skF_3') | ~m1_subset_1(A_1206, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(A_1206, B_1207))), inference(superposition, [status(thm), theory('equality')], [c_25844, c_44896])).
% 16.19/9.14  tff(c_44959, plain, (![A_1206, B_1207]: (r2_hidden('#skF_1'(A_1206, B_1207), k1_xboole_0) | ~r1_tarski(A_1206, '#skF_4') | ~v3_pre_topc(A_1206, '#skF_3') | ~m1_subset_1(A_1206, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_1206, B_1207))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_44937])).
% 16.19/9.14  tff(c_61268, plain, (![A_1438, B_1439]: (~r1_tarski(A_1438, '#skF_4') | ~v3_pre_topc(A_1438, '#skF_3') | ~m1_subset_1(A_1438, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_1438, B_1439))), inference(negUnitSimplification, [status(thm)], [c_27049, c_44959])).
% 16.19/9.14  tff(c_61279, plain, (![B_1439]: (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | r1_tarski('#skF_5', B_1439))), inference(resolution, [status(thm)], [c_25213, c_61268])).
% 16.19/9.14  tff(c_61314, plain, (![B_1440]: (r1_tarski('#skF_5', B_1440))), inference(demodulation, [status(thm), theory('equality')], [c_25177, c_25175, c_61279])).
% 16.19/9.14  tff(c_61559, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_61314, c_16])).
% 16.19/9.14  tff(c_61683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25163, c_61559])).
% 16.19/9.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.19/9.14  
% 16.19/9.14  Inference rules
% 16.19/9.14  ----------------------
% 16.19/9.14  #Ref     : 0
% 16.19/9.14  #Sup     : 13759
% 16.19/9.14  #Fact    : 0
% 16.19/9.14  #Define  : 0
% 16.19/9.14  #Split   : 22
% 16.19/9.14  #Chain   : 0
% 16.19/9.14  #Close   : 0
% 16.19/9.14  
% 16.19/9.14  Ordering : KBO
% 16.19/9.14  
% 16.19/9.14  Simplification rules
% 16.19/9.14  ----------------------
% 16.19/9.14  #Subsume      : 2592
% 16.19/9.14  #Demod        : 12192
% 16.19/9.14  #Tautology    : 4190
% 16.19/9.14  #SimpNegUnit  : 46
% 16.19/9.14  #BackRed      : 23
% 16.19/9.14  
% 16.19/9.14  #Partial instantiations: 0
% 16.19/9.14  #Strategies tried      : 1
% 16.19/9.14  
% 16.19/9.14  Timing (in seconds)
% 16.19/9.14  ----------------------
% 16.19/9.14  Preprocessing        : 0.37
% 16.19/9.14  Parsing              : 0.20
% 16.19/9.14  CNF conversion       : 0.03
% 16.19/9.14  Main loop            : 7.95
% 16.19/9.14  Inferencing          : 1.43
% 16.19/9.14  Reduction            : 3.32
% 16.19/9.14  Demodulation         : 2.72
% 16.19/9.14  BG Simplification    : 0.17
% 16.19/9.14  Subsumption          : 2.55
% 16.19/9.14  Abstraction          : 0.24
% 16.19/9.14  MUC search           : 0.00
% 16.19/9.14  Cooper               : 0.00
% 16.19/9.14  Total                : 8.36
% 16.19/9.14  Index Insertion      : 0.00
% 16.19/9.14  Index Deletion       : 0.00
% 16.19/9.14  Index Matching       : 0.00
% 16.19/9.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
