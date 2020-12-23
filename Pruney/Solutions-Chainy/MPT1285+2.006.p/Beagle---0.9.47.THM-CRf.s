%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:24 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 516 expanded)
%              Number of leaves         :   29 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  403 (2136 expanded)
%              Number of equality atoms :   29 (  76 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_55,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_70,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_205,plain,(
    ! [A_66,B_67] :
      ( k1_tops_1(A_66,k2_pre_topc(A_66,B_67)) = B_67
      | ~ v6_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_213,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_221,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_213])).

tff(c_197,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k2_pre_topc(A_62,B_63),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( v3_pre_topc(k1_tops_1(A_19,B_20),A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_322,plain,(
    ! [A_76,B_77] :
      ( v3_pre_topc(k1_tops_1(A_76,k2_pre_topc(A_76,B_77)),A_76)
      | ~ v2_pre_topc(A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_197,c_26])).

tff(c_325,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_322])).

tff(c_327,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_40,c_325])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_327])).

tff(c_331,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_714,plain,(
    ! [B_125,A_126,C_127] :
      ( r1_tarski(B_125,k1_tops_1(A_126,C_127))
      | ~ r1_tarski(B_125,C_127)
      | ~ v3_pre_topc(B_125,A_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_722,plain,(
    ! [B_125] :
      ( r1_tarski(B_125,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_125,'#skF_3')
      | ~ v3_pre_topc(B_125,'#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_714])).

tff(c_752,plain,(
    ! [B_129] :
      ( r1_tarski(B_129,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_129,'#skF_3')
      | ~ v3_pre_topc(B_129,'#skF_1')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_722])).

tff(c_763,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_752])).

tff(c_772,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_6,c_763])).

tff(c_414,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k1_tops_1(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( r1_tarski(B_10,k2_pre_topc(A_8,B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_570,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(k1_tops_1(A_108,B_109),k2_pre_topc(A_108,k1_tops_1(A_108,B_109)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_414,c_12])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_587,plain,(
    ! [A_3,A_108,B_109] :
      ( r1_tarski(A_3,k2_pre_topc(A_108,k1_tops_1(A_108,B_109)))
      | ~ r1_tarski(A_3,k1_tops_1(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_570,c_8])).

tff(c_330,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_332,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_468,plain,(
    ! [A_94,B_95] :
      ( k1_tops_1(A_94,k2_pre_topc(A_94,B_95)) = B_95
      | ~ v6_tops_1(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_476,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_468])).

tff(c_484,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56,c_476])).

tff(c_856,plain,(
    ! [B_133,A_134] :
      ( v4_tops_1(B_133,A_134)
      | ~ r1_tarski(B_133,k2_pre_topc(A_134,k1_tops_1(A_134,B_133)))
      | ~ r1_tarski(k1_tops_1(A_134,k2_pre_topc(A_134,B_133)),B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_878,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_856])).

tff(c_893,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_6,c_878])).

tff(c_894,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_893])).

tff(c_902,plain,
    ( ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_587,c_894])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_772,c_902])).

tff(c_914,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_916,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_914,c_46])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_917,plain,(
    ! [B_135,A_136] :
      ( r1_tarski(B_135,k2_pre_topc(A_136,B_135))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_919,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_917])).

tff(c_924,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_919])).

tff(c_913,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1250,plain,(
    ! [A_177,B_178] :
      ( k2_pre_topc(A_177,k1_tops_1(A_177,k2_pre_topc(A_177,B_178))) = k2_pre_topc(A_177,B_178)
      | ~ v3_pre_topc(B_178,A_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1256,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1250])).

tff(c_1263,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_916,c_1256])).

tff(c_1043,plain,(
    ! [A_149,B_150] :
      ( m1_subset_1(k1_tops_1(A_149,B_150),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1049,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(k1_tops_1(A_149,B_150),k2_pre_topc(A_149,k1_tops_1(A_149,B_150)))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(resolution,[status(thm)],[c_1043,c_12])).

tff(c_1288,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_1049])).

tff(c_1318,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k2_pre_topc('#skF_2','#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1288])).

tff(c_1331,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1318])).

tff(c_1351,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1331])).

tff(c_1355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1351])).

tff(c_1357,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1318])).

tff(c_1447,plain,(
    ! [B_184,A_185,C_186] :
      ( r1_tarski(B_184,k1_tops_1(A_185,C_186))
      | ~ r1_tarski(B_184,C_186)
      | ~ v3_pre_topc(B_184,A_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1449,plain,(
    ! [B_184] :
      ( r1_tarski(B_184,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_184,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_184,'#skF_2')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1357,c_1447])).

tff(c_2625,plain,(
    ! [B_223] :
      ( r1_tarski(B_223,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_223,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_223,'#skF_2')
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1449])).

tff(c_1175,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_tops_1(A_167,k2_pre_topc(A_167,B_168)),B_168)
      | ~ v4_tops_1(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1190,plain,(
    ! [A_167,B_168] :
      ( k1_tops_1(A_167,k2_pre_topc(A_167,B_168)) = B_168
      | ~ r1_tarski(B_168,k1_tops_1(A_167,k2_pre_topc(A_167,B_168)))
      | ~ v4_tops_1(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_1175,c_2])).

tff(c_2645,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2625,c_1190])).

tff(c_2706,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_916,c_924,c_36,c_913,c_2645])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [B_16,A_14] :
      ( v6_tops_1(B_16,A_14)
      | k1_tops_1(A_14,k2_pre_topc(A_14,B_16)) != B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1299,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_20])).

tff(c_1327,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1299])).

tff(c_2255,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_2258,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2255])).

tff(c_2262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1357,c_2258])).

tff(c_2263,plain,(
    v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_2738,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2706,c_2263])).

tff(c_2746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_2738])).

tff(c_2747,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2763,plain,(
    ! [B_229,A_230] :
      ( r1_tarski(B_229,k2_pre_topc(A_230,B_229))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2765,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_2763])).

tff(c_2770,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2765])).

tff(c_2748,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2749,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2748,c_50])).

tff(c_3042,plain,(
    ! [A_271,B_272] :
      ( k2_pre_topc(A_271,k1_tops_1(A_271,k2_pre_topc(A_271,B_272))) = k2_pre_topc(A_271,B_272)
      | ~ v3_pre_topc(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3048,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_3042])).

tff(c_3055,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2747,c_3048])).

tff(c_3091,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3055,c_20])).

tff(c_3119,plain,
    ( v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3091])).

tff(c_3341,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3119])).

tff(c_3344,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3341])).

tff(c_3347,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3344])).

tff(c_3350,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_3347])).

tff(c_3354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_3350])).

tff(c_3356,plain,(
    m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3119])).

tff(c_3094,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3055,c_10])).

tff(c_3121,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3094])).

tff(c_3429,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3356,c_3121])).

tff(c_28,plain,(
    ! [B_25,A_21,C_27] :
      ( r1_tarski(B_25,k1_tops_1(A_21,C_27))
      | ~ r1_tarski(B_25,C_27)
      | ~ v3_pre_topc(B_25,A_21)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3431,plain,(
    ! [B_25] :
      ( r1_tarski(B_25,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_25,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_25,'#skF_2')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3429,c_28])).

tff(c_4136,plain,(
    ! [B_310] :
      ( r1_tarski(B_310,k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
      | ~ r1_tarski(B_310,k2_pre_topc('#skF_2','#skF_4'))
      | ~ v3_pre_topc(B_310,'#skF_2')
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3431])).

tff(c_2957,plain,(
    ! [A_255,B_256] :
      ( r1_tarski(k1_tops_1(A_255,k2_pre_topc(A_255,B_256)),B_256)
      | ~ v4_tops_1(B_256,A_255)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2969,plain,(
    ! [A_255,B_256] :
      ( k1_tops_1(A_255,k2_pre_topc(A_255,B_256)) = B_256
      | ~ r1_tarski(B_256,k1_tops_1(A_255,k2_pre_topc(A_255,B_256)))
      | ~ v4_tops_1(B_256,A_255)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_2957,c_2])).

tff(c_4151,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4136,c_2969])).

tff(c_4204,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2747,c_2770,c_36,c_2749,c_4151])).

tff(c_3355,plain,(
    v6_tops_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3119])).

tff(c_4240,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_3355])).

tff(c_4246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_4240])).

tff(c_4248,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4259,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4248,c_42])).

tff(c_4260,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4259])).

tff(c_4247,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4399,plain,(
    ! [A_334,B_335] :
      ( k1_tops_1(A_334,k2_pre_topc(A_334,B_335)) = B_335
      | ~ v6_tops_1(B_335,A_334)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4407,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4399])).

tff(c_4415,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4247,c_4407])).

tff(c_4391,plain,(
    ! [A_330,B_331] :
      ( m1_subset_1(k2_pre_topc(A_330,B_331),k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ l1_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4563,plain,(
    ! [A_346,B_347] :
      ( v3_pre_topc(k1_tops_1(A_346,k2_pre_topc(A_346,B_347)),A_346)
      | ~ v2_pre_topc(A_346)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346) ) ),
    inference(resolution,[status(thm)],[c_4391,c_26])).

tff(c_4566,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4415,c_4563])).

tff(c_4571,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_40,c_4566])).

tff(c_4573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4260,c_4571])).

tff(c_4575,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4259])).

tff(c_4977,plain,(
    ! [B_393,A_394,C_395] :
      ( r1_tarski(B_393,k1_tops_1(A_394,C_395))
      | ~ r1_tarski(B_393,C_395)
      | ~ v3_pre_topc(B_393,A_394)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ l1_pre_topc(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4985,plain,(
    ! [B_393] :
      ( r1_tarski(B_393,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_393,'#skF_3')
      | ~ v3_pre_topc(B_393,'#skF_1')
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_4977])).

tff(c_5016,plain,(
    ! [B_397] :
      ( r1_tarski(B_397,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_397,'#skF_3')
      | ~ v3_pre_topc(B_397,'#skF_1')
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4985])).

tff(c_5027,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5016])).

tff(c_5036,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4575,c_6,c_5027])).

tff(c_4710,plain,(
    ! [A_365,B_366] :
      ( m1_subset_1(k1_tops_1(A_365,B_366),k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4785,plain,(
    ! [A_375,B_376] :
      ( r1_tarski(k1_tops_1(A_375,B_376),k2_pre_topc(A_375,k1_tops_1(A_375,B_376)))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375) ) ),
    inference(resolution,[status(thm)],[c_4710,c_12])).

tff(c_4808,plain,(
    ! [A_3,A_375,B_376] :
      ( r1_tarski(A_3,k2_pre_topc(A_375,k1_tops_1(A_375,B_376)))
      | ~ r1_tarski(A_3,k1_tops_1(A_375,B_376))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375) ) ),
    inference(resolution,[status(thm)],[c_4785,c_8])).

tff(c_4574,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4259])).

tff(c_4718,plain,(
    ! [A_369,B_370] :
      ( k1_tops_1(A_369,k2_pre_topc(A_369,B_370)) = B_370
      | ~ v6_tops_1(B_370,A_369)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ l1_pre_topc(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4726,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4718])).

tff(c_4734,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4247,c_4726])).

tff(c_5075,plain,(
    ! [B_399,A_400] :
      ( v4_tops_1(B_399,A_400)
      | ~ r1_tarski(B_399,k2_pre_topc(A_400,k1_tops_1(A_400,B_399)))
      | ~ r1_tarski(k1_tops_1(A_400,k2_pre_topc(A_400,B_399)),B_399)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ l1_pre_topc(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5093,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4734,c_5075])).

tff(c_5110,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_6,c_5093])).

tff(c_5111,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4574,c_5110])).

tff(c_5118,plain,
    ( ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4808,c_5111])).

tff(c_5125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_5036,c_5118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:40:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.27  
% 6.38/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.27  %$ v6_tops_1 > v4_tops_1 > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.38/2.27  
% 6.38/2.27  %Foreground sorts:
% 6.38/2.27  
% 6.38/2.27  
% 6.38/2.27  %Background operators:
% 6.38/2.27  
% 6.38/2.27  
% 6.38/2.27  %Foreground operators:
% 6.38/2.27  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.38/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.27  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 6.38/2.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.38/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.27  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 6.38/2.27  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.38/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.38/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.38/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.38/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.38/2.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.38/2.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.38/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.38/2.27  
% 6.67/2.30  tff(f_133, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 6.67/2.30  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 6.67/2.30  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.67/2.30  tff(f_84, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.67/2.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.67/2.30  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 6.67/2.30  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.67/2.30  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 6.67/2.30  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.67/2.30  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 6.67/2.30  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tops_1)).
% 6.67/2.30  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_48, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_55, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 6.67/2.30  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_44, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_70, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 6.67/2.30  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_52, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_56, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 6.67/2.30  tff(c_205, plain, (![A_66, B_67]: (k1_tops_1(A_66, k2_pre_topc(A_66, B_67))=B_67 | ~v6_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.67/2.30  tff(c_213, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_205])).
% 6.67/2.30  tff(c_221, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_213])).
% 6.67/2.30  tff(c_197, plain, (![A_62, B_63]: (m1_subset_1(k2_pre_topc(A_62, B_63), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.67/2.30  tff(c_26, plain, (![A_19, B_20]: (v3_pre_topc(k1_tops_1(A_19, B_20), A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.67/2.30  tff(c_322, plain, (![A_76, B_77]: (v3_pre_topc(k1_tops_1(A_76, k2_pre_topc(A_76, B_77)), A_76) | ~v2_pre_topc(A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_197, c_26])).
% 6.67/2.30  tff(c_325, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_221, c_322])).
% 6.67/2.30  tff(c_327, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_40, c_325])).
% 6.67/2.30  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_327])).
% 6.67/2.30  tff(c_331, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 6.67/2.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.67/2.30  tff(c_714, plain, (![B_125, A_126, C_127]: (r1_tarski(B_125, k1_tops_1(A_126, C_127)) | ~r1_tarski(B_125, C_127) | ~v3_pre_topc(B_125, A_126) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.67/2.30  tff(c_722, plain, (![B_125]: (r1_tarski(B_125, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_125, '#skF_3') | ~v3_pre_topc(B_125, '#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_714])).
% 6.67/2.30  tff(c_752, plain, (![B_129]: (r1_tarski(B_129, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_129, '#skF_3') | ~v3_pre_topc(B_129, '#skF_1') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_722])).
% 6.67/2.30  tff(c_763, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_752])).
% 6.67/2.30  tff(c_772, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_6, c_763])).
% 6.67/2.30  tff(c_414, plain, (![A_88, B_89]: (m1_subset_1(k1_tops_1(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.67/2.30  tff(c_12, plain, (![B_10, A_8]: (r1_tarski(B_10, k2_pre_topc(A_8, B_10)) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.67/2.30  tff(c_570, plain, (![A_108, B_109]: (r1_tarski(k1_tops_1(A_108, B_109), k2_pre_topc(A_108, k1_tops_1(A_108, B_109))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_414, c_12])).
% 6.67/2.30  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.67/2.30  tff(c_587, plain, (![A_3, A_108, B_109]: (r1_tarski(A_3, k2_pre_topc(A_108, k1_tops_1(A_108, B_109))) | ~r1_tarski(A_3, k1_tops_1(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_570, c_8])).
% 6.67/2.30  tff(c_330, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 6.67/2.30  tff(c_332, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_330])).
% 6.67/2.30  tff(c_468, plain, (![A_94, B_95]: (k1_tops_1(A_94, k2_pre_topc(A_94, B_95))=B_95 | ~v6_tops_1(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.67/2.30  tff(c_476, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_468])).
% 6.67/2.30  tff(c_484, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56, c_476])).
% 6.67/2.30  tff(c_856, plain, (![B_133, A_134]: (v4_tops_1(B_133, A_134) | ~r1_tarski(B_133, k2_pre_topc(A_134, k1_tops_1(A_134, B_133))) | ~r1_tarski(k1_tops_1(A_134, k2_pre_topc(A_134, B_133)), B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.67/2.30  tff(c_878, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_484, c_856])).
% 6.67/2.30  tff(c_893, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_6, c_878])).
% 6.67/2.30  tff(c_894, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_332, c_893])).
% 6.67/2.30  tff(c_902, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_587, c_894])).
% 6.67/2.30  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_772, c_902])).
% 6.67/2.30  tff(c_914, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_330])).
% 6.67/2.30  tff(c_46, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_916, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_914, c_46])).
% 6.67/2.30  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_917, plain, (![B_135, A_136]: (r1_tarski(B_135, k2_pre_topc(A_136, B_135)) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.67/2.30  tff(c_919, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_917])).
% 6.67/2.30  tff(c_924, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_919])).
% 6.67/2.30  tff(c_913, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_330])).
% 6.67/2.30  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.67/2.30  tff(c_1250, plain, (![A_177, B_178]: (k2_pre_topc(A_177, k1_tops_1(A_177, k2_pre_topc(A_177, B_178)))=k2_pre_topc(A_177, B_178) | ~v3_pre_topc(B_178, A_177) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.67/2.30  tff(c_1256, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1250])).
% 6.67/2.30  tff(c_1263, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_916, c_1256])).
% 6.67/2.30  tff(c_1043, plain, (![A_149, B_150]: (m1_subset_1(k1_tops_1(A_149, B_150), k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.67/2.30  tff(c_1049, plain, (![A_149, B_150]: (r1_tarski(k1_tops_1(A_149, B_150), k2_pre_topc(A_149, k1_tops_1(A_149, B_150))) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(resolution, [status(thm)], [c_1043, c_12])).
% 6.67/2.30  tff(c_1288, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1263, c_1049])).
% 6.67/2.30  tff(c_1318, plain, (r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k2_pre_topc('#skF_2', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1288])).
% 6.67/2.30  tff(c_1331, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1318])).
% 6.67/2.30  tff(c_1351, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_1331])).
% 6.67/2.30  tff(c_1355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1351])).
% 6.67/2.30  tff(c_1357, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1318])).
% 6.67/2.30  tff(c_1447, plain, (![B_184, A_185, C_186]: (r1_tarski(B_184, k1_tops_1(A_185, C_186)) | ~r1_tarski(B_184, C_186) | ~v3_pre_topc(B_184, A_185) | ~m1_subset_1(C_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.67/2.30  tff(c_1449, plain, (![B_184]: (r1_tarski(B_184, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_184, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_184, '#skF_2') | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1357, c_1447])).
% 6.67/2.30  tff(c_2625, plain, (![B_223]: (r1_tarski(B_223, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_223, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_223, '#skF_2') | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1449])).
% 6.67/2.30  tff(c_1175, plain, (![A_167, B_168]: (r1_tarski(k1_tops_1(A_167, k2_pre_topc(A_167, B_168)), B_168) | ~v4_tops_1(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.67/2.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.67/2.30  tff(c_1190, plain, (![A_167, B_168]: (k1_tops_1(A_167, k2_pre_topc(A_167, B_168))=B_168 | ~r1_tarski(B_168, k1_tops_1(A_167, k2_pre_topc(A_167, B_168))) | ~v4_tops_1(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_1175, c_2])).
% 6.67/2.30  tff(c_2645, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2625, c_1190])).
% 6.67/2.30  tff(c_2706, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_916, c_924, c_36, c_913, c_2645])).
% 6.67/2.30  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.67/2.30  tff(c_20, plain, (![B_16, A_14]: (v6_tops_1(B_16, A_14) | k1_tops_1(A_14, k2_pre_topc(A_14, B_16))!=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.67/2.30  tff(c_1299, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1263, c_20])).
% 6.67/2.30  tff(c_1327, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1299])).
% 6.67/2.30  tff(c_2255, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1327])).
% 6.67/2.30  tff(c_2258, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2255])).
% 6.67/2.30  tff(c_2262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1357, c_2258])).
% 6.67/2.30  tff(c_2263, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_1327])).
% 6.67/2.30  tff(c_2738, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2706, c_2263])).
% 6.67/2.30  tff(c_2746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_2738])).
% 6.67/2.30  tff(c_2747, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.67/2.30  tff(c_2763, plain, (![B_229, A_230]: (r1_tarski(B_229, k2_pre_topc(A_230, B_229)) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.67/2.30  tff(c_2765, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_2763])).
% 6.67/2.30  tff(c_2770, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2765])).
% 6.67/2.30  tff(c_2748, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 6.67/2.30  tff(c_50, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_2749, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2748, c_50])).
% 6.67/2.30  tff(c_3042, plain, (![A_271, B_272]: (k2_pre_topc(A_271, k1_tops_1(A_271, k2_pre_topc(A_271, B_272)))=k2_pre_topc(A_271, B_272) | ~v3_pre_topc(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.67/2.30  tff(c_3048, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_3042])).
% 6.67/2.30  tff(c_3055, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2747, c_3048])).
% 6.67/2.30  tff(c_3091, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3055, c_20])).
% 6.67/2.30  tff(c_3119, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3091])).
% 6.67/2.30  tff(c_3341, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3119])).
% 6.67/2.30  tff(c_3344, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3341])).
% 6.67/2.30  tff(c_3347, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3344])).
% 6.67/2.30  tff(c_3350, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_3347])).
% 6.67/2.30  tff(c_3354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_3350])).
% 6.67/2.30  tff(c_3356, plain, (m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3119])).
% 6.67/2.30  tff(c_3094, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3055, c_10])).
% 6.67/2.30  tff(c_3121, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3094])).
% 6.67/2.30  tff(c_3429, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3356, c_3121])).
% 6.67/2.30  tff(c_28, plain, (![B_25, A_21, C_27]: (r1_tarski(B_25, k1_tops_1(A_21, C_27)) | ~r1_tarski(B_25, C_27) | ~v3_pre_topc(B_25, A_21) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.67/2.30  tff(c_3431, plain, (![B_25]: (r1_tarski(B_25, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_25, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_25, '#skF_2') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_3429, c_28])).
% 6.67/2.30  tff(c_4136, plain, (![B_310]: (r1_tarski(B_310, k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski(B_310, k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc(B_310, '#skF_2') | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3431])).
% 6.67/2.30  tff(c_2957, plain, (![A_255, B_256]: (r1_tarski(k1_tops_1(A_255, k2_pre_topc(A_255, B_256)), B_256) | ~v4_tops_1(B_256, A_255) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.67/2.30  tff(c_2969, plain, (![A_255, B_256]: (k1_tops_1(A_255, k2_pre_topc(A_255, B_256))=B_256 | ~r1_tarski(B_256, k1_tops_1(A_255, k2_pre_topc(A_255, B_256))) | ~v4_tops_1(B_256, A_255) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_2957, c_2])).
% 6.67/2.30  tff(c_4151, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_4136, c_2969])).
% 6.67/2.30  tff(c_4204, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2747, c_2770, c_36, c_2749, c_4151])).
% 6.67/2.30  tff(c_3355, plain, (v6_tops_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_3119])).
% 6.67/2.30  tff(c_4240, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_3355])).
% 6.67/2.30  tff(c_4246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_4240])).
% 6.67/2.30  tff(c_4248, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.67/2.30  tff(c_42, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.67/2.30  tff(c_4259, plain, (~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4248, c_42])).
% 6.67/2.30  tff(c_4260, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_4259])).
% 6.67/2.30  tff(c_4247, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 6.67/2.30  tff(c_4399, plain, (![A_334, B_335]: (k1_tops_1(A_334, k2_pre_topc(A_334, B_335))=B_335 | ~v6_tops_1(B_335, A_334) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_334))) | ~l1_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.67/2.30  tff(c_4407, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4399])).
% 6.67/2.30  tff(c_4415, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4247, c_4407])).
% 6.67/2.30  tff(c_4391, plain, (![A_330, B_331]: (m1_subset_1(k2_pre_topc(A_330, B_331), k1_zfmisc_1(u1_struct_0(A_330))) | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0(A_330))) | ~l1_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.67/2.30  tff(c_4563, plain, (![A_346, B_347]: (v3_pre_topc(k1_tops_1(A_346, k2_pre_topc(A_346, B_347)), A_346) | ~v2_pre_topc(A_346) | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346))), inference(resolution, [status(thm)], [c_4391, c_26])).
% 6.67/2.30  tff(c_4566, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4415, c_4563])).
% 6.67/2.30  tff(c_4571, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_40, c_4566])).
% 6.67/2.30  tff(c_4573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4260, c_4571])).
% 6.67/2.30  tff(c_4575, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4259])).
% 6.67/2.30  tff(c_4977, plain, (![B_393, A_394, C_395]: (r1_tarski(B_393, k1_tops_1(A_394, C_395)) | ~r1_tarski(B_393, C_395) | ~v3_pre_topc(B_393, A_394) | ~m1_subset_1(C_395, k1_zfmisc_1(u1_struct_0(A_394))) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0(A_394))) | ~l1_pre_topc(A_394))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.67/2.30  tff(c_4985, plain, (![B_393]: (r1_tarski(B_393, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_393, '#skF_3') | ~v3_pre_topc(B_393, '#skF_1') | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_4977])).
% 6.67/2.30  tff(c_5016, plain, (![B_397]: (r1_tarski(B_397, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(B_397, '#skF_3') | ~v3_pre_topc(B_397, '#skF_1') | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4985])).
% 6.67/2.30  tff(c_5027, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_5016])).
% 6.67/2.30  tff(c_5036, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4575, c_6, c_5027])).
% 6.67/2.30  tff(c_4710, plain, (![A_365, B_366]: (m1_subset_1(k1_tops_1(A_365, B_366), k1_zfmisc_1(u1_struct_0(A_365))) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.67/2.30  tff(c_4785, plain, (![A_375, B_376]: (r1_tarski(k1_tops_1(A_375, B_376), k2_pre_topc(A_375, k1_tops_1(A_375, B_376))) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375))), inference(resolution, [status(thm)], [c_4710, c_12])).
% 6.67/2.30  tff(c_4808, plain, (![A_3, A_375, B_376]: (r1_tarski(A_3, k2_pre_topc(A_375, k1_tops_1(A_375, B_376))) | ~r1_tarski(A_3, k1_tops_1(A_375, B_376)) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375))), inference(resolution, [status(thm)], [c_4785, c_8])).
% 6.67/2.30  tff(c_4574, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_4259])).
% 6.67/2.30  tff(c_4718, plain, (![A_369, B_370]: (k1_tops_1(A_369, k2_pre_topc(A_369, B_370))=B_370 | ~v6_tops_1(B_370, A_369) | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0(A_369))) | ~l1_pre_topc(A_369))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.67/2.30  tff(c_4726, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4718])).
% 6.67/2.30  tff(c_4734, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4247, c_4726])).
% 6.67/2.30  tff(c_5075, plain, (![B_399, A_400]: (v4_tops_1(B_399, A_400) | ~r1_tarski(B_399, k2_pre_topc(A_400, k1_tops_1(A_400, B_399))) | ~r1_tarski(k1_tops_1(A_400, k2_pre_topc(A_400, B_399)), B_399) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_400))) | ~l1_pre_topc(A_400))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.67/2.30  tff(c_5093, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4734, c_5075])).
% 6.67/2.30  tff(c_5110, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_6, c_5093])).
% 6.67/2.30  tff(c_5111, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_4574, c_5110])).
% 6.67/2.30  tff(c_5118, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4808, c_5111])).
% 6.67/2.30  tff(c_5125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_5036, c_5118])).
% 6.67/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/2.30  
% 6.67/2.30  Inference rules
% 6.67/2.30  ----------------------
% 6.67/2.30  #Ref     : 0
% 6.67/2.30  #Sup     : 1169
% 6.67/2.30  #Fact    : 0
% 6.67/2.30  #Define  : 0
% 6.67/2.30  #Split   : 89
% 6.67/2.30  #Chain   : 0
% 6.67/2.30  #Close   : 0
% 6.67/2.30  
% 6.67/2.30  Ordering : KBO
% 6.67/2.30  
% 6.67/2.30  Simplification rules
% 6.67/2.30  ----------------------
% 6.67/2.30  #Subsume      : 396
% 6.67/2.30  #Demod        : 624
% 6.67/2.30  #Tautology    : 148
% 6.67/2.30  #SimpNegUnit  : 7
% 6.67/2.30  #BackRed      : 21
% 6.67/2.30  
% 6.67/2.30  #Partial instantiations: 0
% 6.67/2.30  #Strategies tried      : 1
% 6.67/2.30  
% 6.67/2.30  Timing (in seconds)
% 6.67/2.30  ----------------------
% 6.67/2.30  Preprocessing        : 0.31
% 6.67/2.30  Parsing              : 0.18
% 6.67/2.30  CNF conversion       : 0.02
% 6.67/2.30  Main loop            : 1.19
% 6.67/2.30  Inferencing          : 0.34
% 6.67/2.30  Reduction            : 0.39
% 6.67/2.30  Demodulation         : 0.26
% 6.67/2.30  BG Simplification    : 0.04
% 6.67/2.30  Subsumption          : 0.33
% 6.67/2.30  Abstraction          : 0.06
% 6.67/2.30  MUC search           : 0.00
% 6.67/2.30  Cooper               : 0.00
% 6.67/2.30  Total                : 1.56
% 6.67/2.30  Index Insertion      : 0.00
% 6.67/2.30  Index Deletion       : 0.00
% 6.67/2.30  Index Matching       : 0.00
% 6.67/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
