%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:27 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 941 expanded)
%              Number of leaves         :   32 ( 369 expanded)
%              Depth                    :   18
%              Number of atoms          :  269 (5268 expanded)
%              Number of equality atoms :   18 ( 798 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                   => ~ ( ! [E] :
                            ( m1_subset_1(E,u1_struct_0(B))
                           => E != D )
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(C))
                           => E != D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_3110,plain,(
    ! [A_330,B_331,C_332] :
      ( m1_pre_topc(k1_tsep_1(A_330,B_331,C_332),A_330)
      | ~ m1_pre_topc(C_332,A_330)
      | v2_struct_0(C_332)
      | ~ m1_pre_topc(B_331,A_330)
      | v2_struct_0(B_331)
      | ~ l1_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3115,plain,(
    ! [A_333,B_334,C_335] :
      ( l1_pre_topc(k1_tsep_1(A_333,B_334,C_335))
      | ~ m1_pre_topc(C_335,A_333)
      | v2_struct_0(C_335)
      | ~ m1_pre_topc(B_334,A_333)
      | v2_struct_0(B_334)
      | ~ l1_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(resolution,[status(thm)],[c_3110,c_36])).

tff(c_34,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_60,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_30,plain,(
    ! [B_12,A_11] :
      ( v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_145,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_30])).

tff(c_187,plain,(
    ~ v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_593,plain,(
    ! [A_196,C_197,B_198] :
      ( k1_tsep_1(A_196,C_197,B_198) = k1_tsep_1(A_196,B_198,C_197)
      | ~ m1_pre_topc(C_197,A_196)
      | v2_struct_0(C_197)
      | ~ m1_pre_topc(B_198,A_196)
      | v2_struct_0(B_198)
      | ~ l1_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_597,plain,(
    ! [B_198] :
      ( k1_tsep_1('#skF_3',B_198,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_198)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_198,'#skF_3')
      | v2_struct_0(B_198)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_593])).

tff(c_603,plain,(
    ! [B_198] :
      ( k1_tsep_1('#skF_3',B_198,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_198)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_198,'#skF_3')
      | v2_struct_0(B_198)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_597])).

tff(c_609,plain,(
    ! [B_199] :
      ( k1_tsep_1('#skF_3',B_199,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_199)
      | ~ m1_pre_topc(B_199,'#skF_3')
      | v2_struct_0(B_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66,c_603])).

tff(c_619,plain,
    ( k1_tsep_1('#skF_3','#skF_5','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_609])).

tff(c_630,plain,(
    k1_tsep_1('#skF_3','#skF_5','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_619])).

tff(c_50,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ v2_struct_0(k1_tsep_1(A_38,B_39,C_40))
      | ~ m1_pre_topc(C_40,A_38)
      | v2_struct_0(C_40)
      | ~ m1_pre_topc(B_39,A_38)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_646,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_50])).

tff(c_662,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_68,c_646])).

tff(c_663,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66,c_70,c_662])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40] :
      ( v1_pre_topc(k1_tsep_1(A_38,B_39,C_40))
      | ~ m1_pre_topc(C_40,A_38)
      | v2_struct_0(C_40)
      | ~ m1_pre_topc(B_39,A_38)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_643,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_48])).

tff(c_659,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_68,c_643])).

tff(c_660,plain,(
    v1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66,c_70,c_659])).

tff(c_46,plain,(
    ! [A_38,B_39,C_40] :
      ( m1_pre_topc(k1_tsep_1(A_38,B_39,C_40),A_38)
      | ~ m1_pre_topc(C_40,A_38)
      | v2_struct_0(C_40)
      | ~ m1_pre_topc(B_39,A_38)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_640,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_46])).

tff(c_656,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_68,c_640])).

tff(c_657,plain,(
    m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66,c_70,c_656])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1189,plain,(
    ! [A_221,B_222,C_223] :
      ( u1_struct_0(k1_tsep_1(A_221,B_222,C_223)) = k2_xboole_0(u1_struct_0(B_222),u1_struct_0(C_223))
      | ~ m1_pre_topc(k1_tsep_1(A_221,B_222,C_223),A_221)
      | ~ v1_pre_topc(k1_tsep_1(A_221,B_222,C_223))
      | v2_struct_0(k1_tsep_1(A_221,B_222,C_223))
      | ~ m1_pre_topc(C_223,A_221)
      | v2_struct_0(C_223)
      | ~ m1_pre_topc(B_222,A_221)
      | v2_struct_0(B_222)
      | ~ l1_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1205,plain,
    ( k2_xboole_0(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) = u1_struct_0(k1_tsep_1('#skF_3','#skF_5','#skF_4'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v1_pre_topc(k1_tsep_1('#skF_3','#skF_5','#skF_4'))
    | v2_struct_0(k1_tsep_1('#skF_3','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_1189])).

tff(c_1233,plain,
    ( k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) = u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_64,c_68,c_630,c_660,c_630,c_657,c_630,c_2,c_1205])).

tff(c_1234,plain,(
    k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) = u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66,c_70,c_663,c_1233])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_210,plain,(
    ! [D_117,B_118,A_119] :
      ( r2_hidden(D_117,B_118)
      | r2_hidden(D_117,A_119)
      | ~ r2_hidden(D_117,k2_xboole_0(A_119,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_227,plain,(
    ! [B_12,B_118,A_119] :
      ( r2_hidden(B_12,B_118)
      | r2_hidden(B_12,A_119)
      | ~ m1_subset_1(B_12,k2_xboole_0(A_119,B_118))
      | v1_xboole_0(k2_xboole_0(A_119,B_118)) ) ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_1288,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,u1_struct_0('#skF_5'))
      | r2_hidden(B_12,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_12,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | v1_xboole_0(k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1234,c_227])).

tff(c_1330,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,u1_struct_0('#skF_5'))
      | r2_hidden(B_12,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_12,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1288])).

tff(c_2590,plain,(
    ! [B_261] :
      ( r2_hidden(B_261,u1_struct_0('#skF_5'))
      | r2_hidden(B_261,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_261,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1330])).

tff(c_2626,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_2590])).

tff(c_2628,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2626])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2634,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2628,c_32])).

tff(c_2639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2634])).

tff(c_2640,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2626])).

tff(c_2790,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2640,c_32])).

tff(c_2795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2790])).

tff(c_2797,plain,(
    v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_38,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2801,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2797,c_38])).

tff(c_2844,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2801])).

tff(c_2848,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_2844])).

tff(c_3118,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3115,c_2848])).

tff(c_3121,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_64,c_3118])).

tff(c_3123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_66,c_3121])).

tff(c_3124,plain,(
    v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2801])).

tff(c_3321,plain,(
    ! [A_381,B_382,C_383] :
      ( ~ v2_struct_0(k1_tsep_1(A_381,B_382,C_383))
      | ~ m1_pre_topc(C_383,A_381)
      | v2_struct_0(C_383)
      | ~ m1_pre_topc(B_382,A_381)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3324,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3124,c_3321])).

tff(c_3327,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_64,c_3324])).

tff(c_3329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_66,c_3327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:35:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.16  
% 5.84/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.16  %$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.84/2.16  
% 5.84/2.16  %Foreground sorts:
% 5.84/2.16  
% 5.84/2.16  
% 5.84/2.16  %Background operators:
% 5.84/2.16  
% 5.84/2.16  
% 5.84/2.16  %Foreground operators:
% 5.84/2.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.84/2.16  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 5.84/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.84/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.84/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.84/2.16  tff('#skF_6', type, '#skF_6': $i).
% 5.84/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.84/2.16  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.84/2.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.84/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.84/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.16  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.84/2.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.84/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.84/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.84/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.84/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.16  
% 6.20/2.18  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (m1_subset_1(D, u1_struct_0(k1_tsep_1(A, B, C))) => ~((![E]: (m1_subset_1(E, u1_struct_0(B)) => ~(E = D))) & (![E]: (m1_subset_1(E, u1_struct_0(C)) => ~(E = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tmap_1)).
% 6.20/2.18  tff(f_146, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 6.20/2.18  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.20/2.18  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.20/2.18  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.20/2.18  tff(f_95, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => (k1_tsep_1(A, B, C) = k1_tsep_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k1_tsep_1)).
% 6.20/2.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.20/2.18  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 6.20/2.18  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.20/2.18  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.20/2.18  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.20/2.18  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_3110, plain, (![A_330, B_331, C_332]: (m1_pre_topc(k1_tsep_1(A_330, B_331, C_332), A_330) | ~m1_pre_topc(C_332, A_330) | v2_struct_0(C_332) | ~m1_pre_topc(B_331, A_330) | v2_struct_0(B_331) | ~l1_pre_topc(A_330) | v2_struct_0(A_330))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.20/2.18  tff(c_36, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.20/2.18  tff(c_3115, plain, (![A_333, B_334, C_335]: (l1_pre_topc(k1_tsep_1(A_333, B_334, C_335)) | ~m1_pre_topc(C_335, A_333) | v2_struct_0(C_335) | ~m1_pre_topc(B_334, A_333) | v2_struct_0(B_334) | ~l1_pre_topc(A_333) | v2_struct_0(A_333))), inference(resolution, [status(thm)], [c_3110, c_36])).
% 6.20/2.18  tff(c_34, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.20/2.18  tff(c_58, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_60, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 6.20/2.18  tff(c_30, plain, (![B_12, A_11]: (v1_xboole_0(B_12) | ~m1_subset_1(B_12, A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.20/2.18  tff(c_145, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_62, c_30])).
% 6.20/2.18  tff(c_187, plain, (~v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_145])).
% 6.20/2.18  tff(c_593, plain, (![A_196, C_197, B_198]: (k1_tsep_1(A_196, C_197, B_198)=k1_tsep_1(A_196, B_198, C_197) | ~m1_pre_topc(C_197, A_196) | v2_struct_0(C_197) | ~m1_pre_topc(B_198, A_196) | v2_struct_0(B_198) | ~l1_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.20/2.18  tff(c_597, plain, (![B_198]: (k1_tsep_1('#skF_3', B_198, '#skF_5')=k1_tsep_1('#skF_3', '#skF_5', B_198) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_198, '#skF_3') | v2_struct_0(B_198) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_593])).
% 6.20/2.18  tff(c_603, plain, (![B_198]: (k1_tsep_1('#skF_3', B_198, '#skF_5')=k1_tsep_1('#skF_3', '#skF_5', B_198) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_198, '#skF_3') | v2_struct_0(B_198) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_597])).
% 6.20/2.18  tff(c_609, plain, (![B_199]: (k1_tsep_1('#skF_3', B_199, '#skF_5')=k1_tsep_1('#skF_3', '#skF_5', B_199) | ~m1_pre_topc(B_199, '#skF_3') | v2_struct_0(B_199))), inference(negUnitSimplification, [status(thm)], [c_76, c_66, c_603])).
% 6.20/2.18  tff(c_619, plain, (k1_tsep_1('#skF_3', '#skF_5', '#skF_4')=k1_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_609])).
% 6.20/2.18  tff(c_630, plain, (k1_tsep_1('#skF_3', '#skF_5', '#skF_4')=k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_619])).
% 6.20/2.18  tff(c_50, plain, (![A_38, B_39, C_40]: (~v2_struct_0(k1_tsep_1(A_38, B_39, C_40)) | ~m1_pre_topc(C_40, A_38) | v2_struct_0(C_40) | ~m1_pre_topc(B_39, A_38) | v2_struct_0(B_39) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.20/2.18  tff(c_646, plain, (~v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_630, c_50])).
% 6.20/2.18  tff(c_662, plain, (~v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_68, c_646])).
% 6.20/2.18  tff(c_663, plain, (~v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_66, c_70, c_662])).
% 6.20/2.18  tff(c_48, plain, (![A_38, B_39, C_40]: (v1_pre_topc(k1_tsep_1(A_38, B_39, C_40)) | ~m1_pre_topc(C_40, A_38) | v2_struct_0(C_40) | ~m1_pre_topc(B_39, A_38) | v2_struct_0(B_39) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.20/2.18  tff(c_643, plain, (v1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_630, c_48])).
% 6.20/2.18  tff(c_659, plain, (v1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_68, c_643])).
% 6.20/2.18  tff(c_660, plain, (v1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_66, c_70, c_659])).
% 6.20/2.18  tff(c_46, plain, (![A_38, B_39, C_40]: (m1_pre_topc(k1_tsep_1(A_38, B_39, C_40), A_38) | ~m1_pre_topc(C_40, A_38) | v2_struct_0(C_40) | ~m1_pre_topc(B_39, A_38) | v2_struct_0(B_39) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.20/2.18  tff(c_640, plain, (m1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_630, c_46])).
% 6.20/2.18  tff(c_656, plain, (m1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_68, c_640])).
% 6.20/2.18  tff(c_657, plain, (m1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_66, c_70, c_656])).
% 6.20/2.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.20/2.18  tff(c_1189, plain, (![A_221, B_222, C_223]: (u1_struct_0(k1_tsep_1(A_221, B_222, C_223))=k2_xboole_0(u1_struct_0(B_222), u1_struct_0(C_223)) | ~m1_pre_topc(k1_tsep_1(A_221, B_222, C_223), A_221) | ~v1_pre_topc(k1_tsep_1(A_221, B_222, C_223)) | v2_struct_0(k1_tsep_1(A_221, B_222, C_223)) | ~m1_pre_topc(C_223, A_221) | v2_struct_0(C_223) | ~m1_pre_topc(B_222, A_221) | v2_struct_0(B_222) | ~l1_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.20/2.18  tff(c_1205, plain, (k2_xboole_0(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))=u1_struct_0(k1_tsep_1('#skF_3', '#skF_5', '#skF_4')) | ~m1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~v1_pre_topc(k1_tsep_1('#skF_3', '#skF_5', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_630, c_1189])).
% 6.20/2.18  tff(c_1233, plain, (k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))=u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_64, c_68, c_630, c_660, c_630, c_657, c_630, c_2, c_1205])).
% 6.20/2.18  tff(c_1234, plain, (k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))=u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_66, c_70, c_663, c_1233])).
% 6.20/2.18  tff(c_26, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.20/2.18  tff(c_210, plain, (![D_117, B_118, A_119]: (r2_hidden(D_117, B_118) | r2_hidden(D_117, A_119) | ~r2_hidden(D_117, k2_xboole_0(A_119, B_118)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.20/2.18  tff(c_227, plain, (![B_12, B_118, A_119]: (r2_hidden(B_12, B_118) | r2_hidden(B_12, A_119) | ~m1_subset_1(B_12, k2_xboole_0(A_119, B_118)) | v1_xboole_0(k2_xboole_0(A_119, B_118)))), inference(resolution, [status(thm)], [c_26, c_210])).
% 6.20/2.18  tff(c_1288, plain, (![B_12]: (r2_hidden(B_12, u1_struct_0('#skF_5')) | r2_hidden(B_12, u1_struct_0('#skF_4')) | ~m1_subset_1(B_12, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))) | v1_xboole_0(k2_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_1234, c_227])).
% 6.20/2.18  tff(c_1330, plain, (![B_12]: (r2_hidden(B_12, u1_struct_0('#skF_5')) | r2_hidden(B_12, u1_struct_0('#skF_4')) | ~m1_subset_1(B_12, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1288])).
% 6.20/2.18  tff(c_2590, plain, (![B_261]: (r2_hidden(B_261, u1_struct_0('#skF_5')) | r2_hidden(B_261, u1_struct_0('#skF_4')) | ~m1_subset_1(B_261, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_187, c_1330])).
% 6.20/2.18  tff(c_2626, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5')) | r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_2590])).
% 6.20/2.18  tff(c_2628, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_2626])).
% 6.20/2.18  tff(c_32, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.20/2.18  tff(c_2634, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2628, c_32])).
% 6.20/2.18  tff(c_2639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2634])).
% 6.20/2.18  tff(c_2640, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2626])).
% 6.20/2.18  tff(c_2790, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2640, c_32])).
% 6.20/2.18  tff(c_2795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2790])).
% 6.20/2.18  tff(c_2797, plain, (v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_145])).
% 6.20/2.18  tff(c_38, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.20/2.18  tff(c_2801, plain, (~l1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2797, c_38])).
% 6.20/2.18  tff(c_2844, plain, (~l1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2801])).
% 6.20/2.18  tff(c_2848, plain, (~l1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_2844])).
% 6.20/2.18  tff(c_3118, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3115, c_2848])).
% 6.20/2.18  tff(c_3121, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_64, c_3118])).
% 6.20/2.18  tff(c_3123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_66, c_3121])).
% 6.20/2.18  tff(c_3124, plain, (v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_2801])).
% 6.20/2.18  tff(c_3321, plain, (![A_381, B_382, C_383]: (~v2_struct_0(k1_tsep_1(A_381, B_382, C_383)) | ~m1_pre_topc(C_383, A_381) | v2_struct_0(C_383) | ~m1_pre_topc(B_382, A_381) | v2_struct_0(B_382) | ~l1_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.20/2.18  tff(c_3324, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3124, c_3321])).
% 6.20/2.18  tff(c_3327, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_64, c_3324])).
% 6.20/2.18  tff(c_3329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_66, c_3327])).
% 6.20/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.18  
% 6.20/2.18  Inference rules
% 6.20/2.18  ----------------------
% 6.20/2.18  #Ref     : 0
% 6.20/2.18  #Sup     : 686
% 6.20/2.18  #Fact    : 6
% 6.20/2.18  #Define  : 0
% 6.20/2.18  #Split   : 5
% 6.20/2.18  #Chain   : 0
% 6.20/2.18  #Close   : 0
% 6.20/2.18  
% 6.20/2.18  Ordering : KBO
% 6.20/2.18  
% 6.20/2.18  Simplification rules
% 6.20/2.18  ----------------------
% 6.20/2.18  #Subsume      : 116
% 6.20/2.18  #Demod        : 271
% 6.20/2.18  #Tautology    : 163
% 6.20/2.18  #SimpNegUnit  : 129
% 6.20/2.18  #BackRed      : 2
% 6.20/2.18  
% 6.20/2.18  #Partial instantiations: 0
% 6.20/2.18  #Strategies tried      : 1
% 6.20/2.18  
% 6.20/2.18  Timing (in seconds)
% 6.20/2.18  ----------------------
% 6.28/2.18  Preprocessing        : 0.35
% 6.28/2.18  Parsing              : 0.19
% 6.28/2.18  CNF conversion       : 0.03
% 6.28/2.18  Main loop            : 1.06
% 6.28/2.18  Inferencing          : 0.31
% 6.28/2.18  Reduction            : 0.33
% 6.28/2.18  Demodulation         : 0.24
% 6.28/2.18  BG Simplification    : 0.04
% 6.28/2.18  Subsumption          : 0.29
% 6.28/2.18  Abstraction          : 0.05
% 6.28/2.18  MUC search           : 0.00
% 6.28/2.18  Cooper               : 0.00
% 6.28/2.18  Total                : 1.44
% 6.28/2.18  Index Insertion      : 0.00
% 6.28/2.18  Index Deletion       : 0.00
% 6.28/2.18  Index Matching       : 0.00
% 6.28/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
