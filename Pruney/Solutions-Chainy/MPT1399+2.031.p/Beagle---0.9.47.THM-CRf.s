%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 313 expanded)
%              Number of leaves         :   45 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 910 expanded)
%              Number of equality atoms :   13 ( 118 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_99,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_84,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_82,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_100,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2])).

tff(c_16,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | A_11 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_64,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_117,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_128,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_132,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_128])).

tff(c_268,plain,(
    ! [A_95] :
      ( m1_subset_1('#skF_5'(A_95),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_273,plain,
    ( m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_268])).

tff(c_276,plain,
    ( m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_273])).

tff(c_277,plain,(
    m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_276])).

tff(c_12,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_290,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
      | ~ r2_hidden(A_6,'#skF_5'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_277,c_12])).

tff(c_293,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_139,plain,(
    m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_80])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    ! [A_40] :
      ( v4_pre_topc(k2_struct_0(A_40),A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_171,plain,(
    ! [A_71] :
      ( r2_hidden(u1_struct_0(A_71),u1_pre_topc(A_71))
      | ~ v2_pre_topc(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_177,plain,
    ( r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_171])).

tff(c_180,plain,(
    r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_177])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_350,plain,(
    ! [B_101,A_102] :
      ( v3_pre_topc(B_101,A_102)
      | ~ r2_hidden(B_101,u1_pre_topc(A_102))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_440,plain,(
    ! [A_109] :
      ( v3_pre_topc(u1_struct_0(A_109),A_109)
      | ~ r2_hidden(u1_struct_0(A_109),u1_pre_topc(A_109))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_98,c_350])).

tff(c_449,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_440])).

tff(c_456,plain,(
    v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_180,c_132,c_449])).

tff(c_92,plain,(
    ! [D_54] :
      ( v4_pre_topc(D_54,'#skF_6')
      | ~ r2_hidden(D_54,'#skF_8')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_152,plain,(
    ! [D_67] :
      ( v4_pre_topc(D_67,'#skF_6')
      | ~ r2_hidden(D_67,'#skF_8')
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92])).

tff(c_157,plain,
    ( v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_152])).

tff(c_165,plain,(
    ~ r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_88,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_8')
      | ~ r2_hidden('#skF_7',D_54)
      | ~ v4_pre_topc(D_54,'#skF_6')
      | ~ v3_pre_topc(D_54,'#skF_6')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_295,plain,(
    ! [D_96] :
      ( r2_hidden(D_96,'#skF_8')
      | ~ r2_hidden('#skF_7',D_96)
      | ~ v4_pre_topc(D_96,'#skF_6')
      | ~ v3_pre_topc(D_96,'#skF_6')
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_88])).

tff(c_302,plain,
    ( r2_hidden(k2_struct_0('#skF_6'),'#skF_8')
    | ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_295])).

tff(c_306,plain,
    ( ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_302])).

tff(c_491,plain,
    ( ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_306])).

tff(c_492,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_513,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_492])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_513])).

tff(c_518,plain,(
    ~ r2_hidden('#skF_7',k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_522,plain,
    ( v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_518])).

tff(c_525,plain,(
    v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_522])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_525])).

tff(c_610,plain,(
    ! [A_123] : ~ r2_hidden(A_123,'#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_620,plain,(
    '#skF_5'('#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_97,c_610])).

tff(c_72,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0('#skF_5'(A_41))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_641,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_72])).

tff(c_654,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_100,c_641])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_654])).

tff(c_658,plain,(
    r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_661,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_658,c_14])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.43  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.83/1.43  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.83/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.83/1.43  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.83/1.43  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.83/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.83/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.83/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.83/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.83/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.43  
% 2.83/1.45  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.83/1.45  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.83/1.45  tff(f_66, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.83/1.45  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.83/1.45  tff(f_95, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.83/1.45  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.83/1.45  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.83/1.45  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.83/1.45  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.83/1.45  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.83/1.45  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.83/1.45  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.83/1.45  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.83/1.45  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.83/1.45  tff(c_76, plain, (k1_xboole_0='#skF_8'), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.83/1.45  tff(c_99, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4])).
% 2.83/1.45  tff(c_86, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_84, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_82, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.83/1.45  tff(c_100, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2])).
% 2.83/1.45  tff(c_16, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.45  tff(c_97, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | A_11='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16])).
% 2.83/1.45  tff(c_64, plain, (![A_39]: (l1_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.83/1.45  tff(c_117, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.45  tff(c_128, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_64, c_117])).
% 2.83/1.45  tff(c_132, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_82, c_128])).
% 2.83/1.45  tff(c_268, plain, (![A_95]: (m1_subset_1('#skF_5'(A_95), k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.45  tff(c_273, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_132, c_268])).
% 2.83/1.45  tff(c_276, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_273])).
% 2.83/1.45  tff(c_277, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_86, c_276])).
% 2.83/1.45  tff(c_12, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.45  tff(c_290, plain, (![A_6]: (~v1_xboole_0(k2_struct_0('#skF_6')) | ~r2_hidden(A_6, '#skF_5'('#skF_6')))), inference(resolution, [status(thm)], [c_277, c_12])).
% 2.83/1.45  tff(c_293, plain, (~v1_xboole_0(k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.83/1.45  tff(c_80, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_139, plain, (m1_subset_1('#skF_7', k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_80])).
% 2.83/1.45  tff(c_10, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.45  tff(c_66, plain, (![A_40]: (v4_pre_topc(k2_struct_0(A_40), A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.83/1.45  tff(c_171, plain, (![A_71]: (r2_hidden(u1_struct_0(A_71), u1_pre_topc(A_71)) | ~v2_pre_topc(A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.83/1.45  tff(c_177, plain, (r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_132, c_171])).
% 2.83/1.45  tff(c_180, plain, (r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84, c_177])).
% 2.83/1.45  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.83/1.45  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.45  tff(c_98, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.83/1.45  tff(c_350, plain, (![B_101, A_102]: (v3_pre_topc(B_101, A_102) | ~r2_hidden(B_101, u1_pre_topc(A_102)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.83/1.45  tff(c_440, plain, (![A_109]: (v3_pre_topc(u1_struct_0(A_109), A_109) | ~r2_hidden(u1_struct_0(A_109), u1_pre_topc(A_109)) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_98, c_350])).
% 2.83/1.45  tff(c_449, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_132, c_440])).
% 2.83/1.45  tff(c_456, plain, (v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_180, c_132, c_449])).
% 2.83/1.45  tff(c_92, plain, (![D_54]: (v4_pre_topc(D_54, '#skF_6') | ~r2_hidden(D_54, '#skF_8') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_152, plain, (![D_67]: (v4_pre_topc(D_67, '#skF_6') | ~r2_hidden(D_67, '#skF_8') | ~m1_subset_1(D_67, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92])).
% 2.83/1.45  tff(c_157, plain, (v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_98, c_152])).
% 2.83/1.45  tff(c_165, plain, (~r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_157])).
% 2.83/1.45  tff(c_88, plain, (![D_54]: (r2_hidden(D_54, '#skF_8') | ~r2_hidden('#skF_7', D_54) | ~v4_pre_topc(D_54, '#skF_6') | ~v3_pre_topc(D_54, '#skF_6') | ~m1_subset_1(D_54, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.83/1.45  tff(c_295, plain, (![D_96]: (r2_hidden(D_96, '#skF_8') | ~r2_hidden('#skF_7', D_96) | ~v4_pre_topc(D_96, '#skF_6') | ~v3_pre_topc(D_96, '#skF_6') | ~m1_subset_1(D_96, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_88])).
% 2.83/1.45  tff(c_302, plain, (r2_hidden(k2_struct_0('#skF_6'), '#skF_8') | ~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_98, c_295])).
% 2.83/1.45  tff(c_306, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_165, c_302])).
% 2.83/1.45  tff(c_491, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_306])).
% 2.83/1.45  tff(c_492, plain, (~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_491])).
% 2.83/1.45  tff(c_513, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_66, c_492])).
% 2.83/1.45  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_513])).
% 2.83/1.45  tff(c_518, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_491])).
% 2.83/1.45  tff(c_522, plain, (v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_518])).
% 2.83/1.45  tff(c_525, plain, (v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_522])).
% 2.83/1.45  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_525])).
% 2.83/1.45  tff(c_610, plain, (![A_123]: (~r2_hidden(A_123, '#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_290])).
% 2.83/1.45  tff(c_620, plain, ('#skF_5'('#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_97, c_610])).
% 2.83/1.45  tff(c_72, plain, (![A_41]: (~v1_xboole_0('#skF_5'(A_41)) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.45  tff(c_641, plain, (~v1_xboole_0('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_620, c_72])).
% 2.83/1.45  tff(c_654, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_100, c_641])).
% 2.83/1.45  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_654])).
% 2.83/1.45  tff(c_658, plain, (r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_157])).
% 2.83/1.45  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.45  tff(c_661, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_658, c_14])).
% 2.83/1.45  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_661])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 0
% 2.83/1.45  #Sup     : 108
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 12
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 11
% 2.83/1.45  #Demod        : 96
% 2.83/1.45  #Tautology    : 32
% 2.83/1.45  #SimpNegUnit  : 11
% 2.83/1.45  #BackRed      : 17
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 2.83/1.45  Preprocessing        : 0.35
% 2.83/1.45  Parsing              : 0.18
% 2.83/1.45  CNF conversion       : 0.03
% 2.83/1.45  Main loop            : 0.33
% 2.83/1.45  Inferencing          : 0.11
% 2.83/1.45  Reduction            : 0.11
% 2.83/1.45  Demodulation         : 0.07
% 2.83/1.45  BG Simplification    : 0.02
% 2.83/1.45  Subsumption          : 0.06
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.45  Total                : 0.72
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
