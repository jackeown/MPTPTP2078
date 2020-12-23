%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1707+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:16 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :   91 (1366 expanded)
%              Number of leaves         :   32 ( 532 expanded)
%              Depth                    :   18
%              Number of atoms          :  245 (7798 expanded)
%              Number of equality atoms :   18 (1207 expanded)
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

tff(f_168,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_72,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_126,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_44,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_46,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_394,plain,(
    ! [A_162,C_163,B_164] :
      ( k1_tsep_1(A_162,C_163,B_164) = k1_tsep_1(A_162,B_164,C_163)
      | ~ m1_pre_topc(C_163,A_162)
      | v2_struct_0(C_163)
      | ~ m1_pre_topc(B_164,A_162)
      | v2_struct_0(B_164)
      | ~ l1_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_398,plain,(
    ! [B_164] :
      ( k1_tsep_1('#skF_3',B_164,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_164)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_164,'#skF_3')
      | v2_struct_0(B_164)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_394])).

tff(c_404,plain,(
    ! [B_164] :
      ( k1_tsep_1('#skF_3',B_164,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_164)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_164,'#skF_3')
      | v2_struct_0(B_164)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_398])).

tff(c_410,plain,(
    ! [B_165] :
      ( k1_tsep_1('#skF_3',B_165,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_165)
      | ~ m1_pre_topc(B_165,'#skF_3')
      | v2_struct_0(B_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_404])).

tff(c_420,plain,
    ( k1_tsep_1('#skF_3','#skF_5','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_410])).

tff(c_431,plain,(
    k1_tsep_1('#skF_3','#skF_5','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_420])).

tff(c_379,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_pre_topc(k1_tsep_1(A_153,B_154,C_155),A_153)
      | ~ m1_pre_topc(C_155,A_153)
      | v2_struct_0(C_155)
      | ~ m1_pre_topc(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [B_33,A_31] :
      ( l1_pre_topc(B_33)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_383,plain,(
    ! [A_153,B_154,C_155] :
      ( l1_pre_topc(k1_tsep_1(A_153,B_154,C_155))
      | ~ m1_pre_topc(C_155,A_153)
      | v2_struct_0(C_155)
      | ~ m1_pre_topc(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_379,c_36])).

tff(c_435,plain,
    ( l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_383])).

tff(c_448,plain,
    ( l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_54,c_435])).

tff(c_449,plain,(
    l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_56,c_448])).

tff(c_34,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ v2_struct_0(k1_tsep_1(A_27,B_28,C_29))
      | ~ m1_pre_topc(C_29,A_27)
      | v2_struct_0(C_29)
      | ~ m1_pre_topc(B_28,A_27)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_441,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_32])).

tff(c_454,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_54,c_441])).

tff(c_455,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_56,c_454])).

tff(c_30,plain,(
    ! [A_27,B_28,C_29] :
      ( v1_pre_topc(k1_tsep_1(A_27,B_28,C_29))
      | ~ m1_pre_topc(C_29,A_27)
      | v2_struct_0(C_29)
      | ~ m1_pre_topc(B_28,A_27)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_444,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_30])).

tff(c_457,plain,
    ( v1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_54,c_444])).

tff(c_458,plain,(
    v1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_56,c_457])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29] :
      ( m1_pre_topc(k1_tsep_1(A_27,B_28,C_29),A_27)
      | ~ m1_pre_topc(C_29,A_27)
      | v2_struct_0(C_29)
      | ~ m1_pre_topc(B_28,A_27)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_438,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_28])).

tff(c_451,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_54,c_438])).

tff(c_452,plain,(
    m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_56,c_451])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_xboole_0(B_5,A_4) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1420,plain,(
    ! [A_201,B_202,C_203] :
      ( u1_struct_0(k1_tsep_1(A_201,B_202,C_203)) = k2_xboole_0(u1_struct_0(B_202),u1_struct_0(C_203))
      | ~ m1_pre_topc(k1_tsep_1(A_201,B_202,C_203),A_201)
      | ~ v1_pre_topc(k1_tsep_1(A_201,B_202,C_203))
      | v2_struct_0(k1_tsep_1(A_201,B_202,C_203))
      | ~ m1_pre_topc(C_203,A_201)
      | v2_struct_0(C_203)
      | ~ m1_pre_topc(B_202,A_201)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1446,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_431,c_1420])).

tff(c_1492,plain,
    ( k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) = u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_54,c_431,c_458,c_431,c_452,c_431,c_4,c_1446])).

tff(c_1493,plain,(
    k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) = u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_56,c_455,c_1492])).

tff(c_42,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_153,plain,(
    ! [D_104,B_105,A_106] :
      ( r2_hidden(D_104,B_105)
      | r2_hidden(D_104,A_106)
      | ~ r2_hidden(D_104,k2_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_172,plain,(
    ! [A_37,B_105,A_106] :
      ( r2_hidden(A_37,B_105)
      | r2_hidden(A_37,A_106)
      | v1_xboole_0(k2_xboole_0(A_106,B_105))
      | ~ m1_subset_1(A_37,k2_xboole_0(A_106,B_105)) ) ),
    inference(resolution,[status(thm)],[c_42,c_153])).

tff(c_1509,plain,(
    ! [A_37] :
      ( r2_hidden(A_37,u1_struct_0('#skF_5'))
      | r2_hidden(A_37,u1_struct_0('#skF_4'))
      | v1_xboole_0(k2_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))
      | ~ m1_subset_1(A_37,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1493,c_172])).

tff(c_1534,plain,(
    ! [A_37] :
      ( r2_hidden(A_37,u1_struct_0('#skF_5'))
      | r2_hidden(A_37,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(A_37,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1509])).

tff(c_4002,plain,(
    v1_xboole_0(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1534])).

tff(c_38,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(u1_struct_0(A_34))
      | ~ l1_struct_0(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4049,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4002,c_38])).

tff(c_4052,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_4049])).

tff(c_4055,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_4052])).

tff(c_4059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_4055])).

tff(c_4062,plain,(
    ! [A_279] :
      ( r2_hidden(A_279,u1_struct_0('#skF_5'))
      | r2_hidden(A_279,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_279,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_4121,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_4062])).

tff(c_4122,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4121])).

tff(c_40,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4192,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4122,c_40])).

tff(c_4196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4192])).

tff(c_4197,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4121])).

tff(c_4201,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4197,c_40])).

tff(c_4205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_4201])).

%------------------------------------------------------------------------------
