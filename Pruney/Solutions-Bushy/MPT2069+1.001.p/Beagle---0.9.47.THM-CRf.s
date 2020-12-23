%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2069+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:50 EST 2020

% Result     : Theorem 15.42s
% Output     : CNFRefutation 15.42s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 444 expanded)
%              Number of leaves         :   34 ( 170 expanded)
%              Depth                    :   29
%              Number of atoms          :  523 (2158 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_7 > v4_pre_topc > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_waybel_7,type,(
    r1_waybel_7: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> ! [C] :
                  ( ( ~ v1_xboole_0(C)
                    & v1_subset_1(C,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                 => ( r2_hidden(B,C)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r1_waybel_7(A,C,D)
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow19)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v1_subset_1(D,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r1_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(c_66,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_91,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_136,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,k2_pre_topc(A_89,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_138,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_141,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_148,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_151,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k2_pre_topc(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [B_34,A_32] :
      ( r1_tarski(B_34,k2_pre_topc(A_32,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_195,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_pre_topc(A_98,B_99),k2_pre_topc(A_98,k2_pre_topc(A_98,B_99)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_186,c_32])).

tff(c_294,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k2_pre_topc(A_120,B_121),k2_pre_topc(A_120,k2_pre_topc(A_120,B_121)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_186,c_32])).

tff(c_127,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [A_90,B_91,B_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_92)
      | ~ r1_tarski(A_90,B_92)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_8,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [A_90,B_91,B_4,B_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_4)
      | ~ r1_tarski(B_92,B_4)
      | ~ r1_tarski(A_90,B_92)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_685,plain,(
    ! [A_191,B_192,A_193,B_194] :
      ( r2_hidden('#skF_1'(A_191,B_192),k2_pre_topc(A_193,k2_pre_topc(A_193,B_194)))
      | ~ r1_tarski(A_191,k2_pre_topc(A_193,B_194))
      | r1_tarski(A_191,B_192)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_294,c_166])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_707,plain,(
    ! [A_195,A_196,B_197] :
      ( ~ r1_tarski(A_195,k2_pre_topc(A_196,B_197))
      | r1_tarski(A_195,k2_pre_topc(A_196,k2_pre_topc(A_196,B_197)))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_685,c_10])).

tff(c_197,plain,(
    ! [A_100,B_101,B_102,B_103] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(B_103,B_102)
      | ~ r1_tarski(A_100,B_103)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_207,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_tarski(A_104,'#skF_4')
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_141,c_197])).

tff(c_320,plain,(
    ! [A_122,B_123,B_124] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_124)
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_124)
      | ~ r1_tarski(A_122,'#skF_4')
      | r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_339,plain,(
    ! [B_124,A_122] :
      ( ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_124)
      | ~ r1_tarski(A_122,'#skF_4')
      | r1_tarski(A_122,B_124) ) ),
    inference(resolution,[status(thm)],[c_320,c_10])).

tff(c_771,plain,(
    ! [A_213,A_214,B_215] :
      ( ~ r1_tarski(A_213,'#skF_4')
      | r1_tarski(A_213,k2_pre_topc(A_214,k2_pre_topc(A_214,B_215)))
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc(A_214,B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(resolution,[status(thm)],[c_707,c_339])).

tff(c_780,plain,(
    ! [A_213] :
      ( ~ r1_tarski(A_213,'#skF_4')
      | r1_tarski(A_213,k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_195,c_771])).

tff(c_796,plain,(
    ! [A_213] :
      ( ~ r1_tarski(A_213,'#skF_4')
      | r1_tarski(A_213,k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_780])).

tff(c_804,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_807,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_804])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_807])).

tff(c_813,plain,(
    m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_34,plain,(
    ! [A_35,C_37,B_36] :
      ( m1_subset_1(A_35,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_900,plain,(
    ! [A_216] :
      ( m1_subset_1(A_216,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_216,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_813,c_34])).

tff(c_921,plain,(
    ! [B_4] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_4),u1_struct_0('#skF_3'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_900])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_130,plain,(
    ! [A_3,B_4,B_82] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_82)
      | ~ r1_tarski(A_3,B_82)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_264,plain,(
    ! [A_112,A_113,B_114] :
      ( m1_subset_1(A_112,u1_struct_0(A_113))
      | ~ r2_hidden(A_112,k2_pre_topc(A_113,B_114))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_186,c_34])).

tff(c_605,plain,(
    ! [A_169,B_170,A_171,B_172] :
      ( m1_subset_1('#skF_1'(A_169,B_170),u1_struct_0(A_171))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ r1_tarski(A_169,k2_pre_topc(A_171,B_172))
      | r1_tarski(A_169,B_170) ) ),
    inference(resolution,[status(thm)],[c_130,c_264])).

tff(c_609,plain,(
    ! [A_169,B_170] :
      ( m1_subset_1('#skF_1'(A_169,B_170),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_169,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_169,B_170) ) ),
    inference(resolution,[status(thm)],[c_42,c_605])).

tff(c_613,plain,(
    ! [A_169,B_170] :
      ( m1_subset_1('#skF_1'(A_169,B_170),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_169,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_169,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_609])).

tff(c_383,plain,(
    ! [B_128,A_129,C_130] :
      ( r2_hidden(B_128,'#skF_2'(A_129,B_128,C_130))
      | ~ r2_hidden(C_130,k2_pre_topc(A_129,B_128))
      | ~ m1_subset_1(C_130,u1_struct_0(A_129))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_400,plain,(
    ! [B_128,A_129,A_3,B_4] :
      ( r2_hidden(B_128,'#skF_2'(A_129,B_128,'#skF_1'(A_3,B_4)))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0(A_129))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ r1_tarski(A_3,k2_pre_topc(A_129,B_128))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_130,c_383])).

tff(c_24,plain,(
    ! [A_10,B_22,C_28] :
      ( v13_waybel_0('#skF_2'(A_10,B_22,C_28),k3_yellow_1(k2_struct_0(A_10)))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_10,B_22,C_28] :
      ( v2_waybel_0('#skF_2'(A_10,B_22,C_28),k3_yellow_1(k2_struct_0(A_10)))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_10,B_22,C_28] :
      ( v1_subset_1('#skF_2'(A_10,B_22,C_28),u1_struct_0(k3_yellow_1(k2_struct_0(A_10))))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_10)))))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_551,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_waybel_7(A_147,'#skF_2'(A_147,B_148,C_149),C_149)
      | ~ r2_hidden(C_149,k2_pre_topc(A_147,B_148))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_555,plain,(
    ! [C_149] :
      ( r1_waybel_7('#skF_3','#skF_2'('#skF_3','#skF_4',C_149),C_149)
      | ~ r2_hidden(C_149,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_551])).

tff(c_559,plain,(
    ! [C_149] :
      ( r1_waybel_7('#skF_3','#skF_2'('#skF_3','#skF_4',C_149),C_149)
      | ~ r2_hidden(C_149,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_555])).

tff(c_561,plain,(
    ! [C_150] :
      ( r1_waybel_7('#skF_3','#skF_2'('#skF_3','#skF_4',C_150),C_150)
      | ~ r2_hidden(C_150,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_150,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_559])).

tff(c_88,plain,(
    ! [D_65,C_63] :
      ( v4_pre_topc('#skF_4','#skF_3')
      | r2_hidden(D_65,'#skF_4')
      | ~ r1_waybel_7('#skF_3',C_63,D_65)
      | ~ m1_subset_1(D_65,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(C_63,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_220,plain,(
    ! [D_65,C_63] :
      ( r2_hidden(D_65,'#skF_4')
      | ~ r1_waybel_7('#skF_3',C_63,D_65)
      | ~ m1_subset_1(D_65,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1(C_63,u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0(C_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_88])).

tff(c_5705,plain,(
    ! [C_411] :
      ( r2_hidden(C_411,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_411))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4',C_411),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_411),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_411),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_2'('#skF_3','#skF_4',C_411),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_411))
      | ~ r2_hidden(C_411,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_411,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_561,c_220])).

tff(c_5709,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_2'('#skF_3','#skF_4',C_28),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_5705])).

tff(c_5712,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_2'('#skF_3','#skF_4',C_28),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_5709])).

tff(c_13094,plain,(
    ! [C_580] :
      ( r2_hidden(C_580,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_580))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_580),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_580),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_2'('#skF_3','#skF_4',C_580),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_580))
      | ~ r2_hidden(C_580,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_580,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5712])).

tff(c_13098,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_13094])).

tff(c_13101,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_13098])).

tff(c_19288,plain,(
    ! [C_742] :
      ( r2_hidden(C_742,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_742))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_742),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_742),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_742))
      | ~ r2_hidden(C_742,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_742,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_13101])).

tff(c_19292,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_19288])).

tff(c_19295,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_19292])).

tff(c_20741,plain,(
    ! [C_762] :
      ( r2_hidden(C_762,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_762))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_762),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_762))
      | ~ r2_hidden(C_762,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_762,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_19295])).

tff(c_20745,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_20741])).

tff(c_20748,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_20745])).

tff(c_20750,plain,(
    ! [C_763] :
      ( r2_hidden(C_763,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_763))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_763))
      | ~ r2_hidden(C_763,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_763,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20748])).

tff(c_20755,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_3,B_4)))
      | ~ r2_hidden('#skF_1'(A_3,B_4),k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_3,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_400,c_20750])).

tff(c_20769,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_3,B_4)))
      | ~ r2_hidden('#skF_1'(A_3,B_4),k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_3,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_3,B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_20755])).

tff(c_27545,plain,(
    ! [A_903,B_904] :
      ( r2_hidden('#skF_1'(A_903,B_904),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_903,B_904)))
      | ~ r2_hidden('#skF_1'(A_903,B_904),k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_903,B_904),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_903,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_903,B_904) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20769])).

tff(c_27569,plain,(
    ! [A_905,B_906] :
      ( r2_hidden('#skF_1'(A_905,B_906),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_905,B_906)))
      | ~ m1_subset_1('#skF_1'(A_905,B_906),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_905,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_905,B_906) ) ),
    inference(resolution,[status(thm)],[c_130,c_27545])).

tff(c_27620,plain,(
    ! [A_907,B_908] :
      ( r2_hidden('#skF_1'(A_907,B_908),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_907,B_908)))
      | ~ r1_tarski(A_907,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_907,B_908) ) ),
    inference(resolution,[status(thm)],[c_613,c_27569])).

tff(c_278,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ v1_xboole_0('#skF_2'(A_115,B_116,C_117))
      | ~ r2_hidden(C_117,k2_pre_topc(A_115,B_116))
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_291,plain,(
    ! [A_115,B_116,A_3,B_4] :
      ( ~ v1_xboole_0('#skF_2'(A_115,B_116,'#skF_1'(A_3,B_4)))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ r1_tarski(A_3,k2_pre_topc(A_115,B_116))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_130,c_278])).

tff(c_27628,plain,(
    ! [A_907,B_908] :
      ( ~ m1_subset_1('#skF_1'(A_907,B_908),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_hidden('#skF_1'(A_907,B_908),'#skF_4')
      | ~ r1_tarski(A_907,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_907,B_908) ) ),
    inference(resolution,[status(thm)],[c_27620,c_291])).

tff(c_27642,plain,(
    ! [A_907,B_908] :
      ( ~ m1_subset_1('#skF_1'(A_907,B_908),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r2_hidden('#skF_1'(A_907,B_908),'#skF_4')
      | ~ r1_tarski(A_907,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_907,B_908) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_27628])).

tff(c_27650,plain,(
    ! [A_909,B_910] :
      ( ~ m1_subset_1('#skF_1'(A_909,B_910),u1_struct_0('#skF_3'))
      | r2_hidden('#skF_1'(A_909,B_910),'#skF_4')
      | ~ r1_tarski(A_909,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_909,B_910) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_27642])).

tff(c_27665,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_4),'#skF_4')
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_4) ) ),
    inference(resolution,[status(thm)],[c_921,c_27650])).

tff(c_27701,plain,(
    ! [B_911] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_911),'#skF_4')
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_911) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_27665])).

tff(c_27709,plain,(
    r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_27701,c_10])).

tff(c_27720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_151,c_27709])).

tff(c_27721,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_27783,plain,(
    ! [B_928,A_929] :
      ( v4_pre_topc(B_928,A_929)
      | k2_pre_topc(A_929,B_928) != B_928
      | ~ v2_pre_topc(A_929)
      | ~ m1_subset_1(B_928,k1_zfmisc_1(u1_struct_0(A_929)))
      | ~ l1_pre_topc(A_929) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_27789,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_27783])).

tff(c_27793,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_27721,c_27789])).

tff(c_27795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_27793])).

tff(c_27797,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27806,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_50])).

tff(c_56,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27800,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_56])).

tff(c_27957,plain,(
    ! [A_966,B_967] :
      ( k2_pre_topc(A_966,B_967) = B_967
      | ~ v4_pre_topc(B_967,A_966)
      | ~ m1_subset_1(B_967,k1_zfmisc_1(u1_struct_0(A_966)))
      | ~ l1_pre_topc(A_966) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_27966,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_27957])).

tff(c_27971,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_27797,c_27966])).

tff(c_27915,plain,(
    ! [B_962,A_963] :
      ( r1_tarski(B_962,k2_pre_topc(A_963,B_962))
      | ~ m1_subset_1(B_962,k1_zfmisc_1(u1_struct_0(A_963)))
      | ~ l1_pre_topc(A_963) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_27919,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_27915])).

tff(c_27923,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_27919])).

tff(c_27936,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_27923,c_2])).

tff(c_27951,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_27936])).

tff(c_27972,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27971,c_27951])).

tff(c_27977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_27972])).

tff(c_27978,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_27936])).

tff(c_27796,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_54,plain,
    ( m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27808,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_54])).

tff(c_64,plain,
    ( v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27849,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_64])).

tff(c_62,plain,
    ( v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27822,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_62])).

tff(c_60,plain,
    ( v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27813,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_60])).

tff(c_58,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27890,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_58])).

tff(c_52,plain,
    ( r1_waybel_7('#skF_3','#skF_5','#skF_6')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_27810,plain,(
    r1_waybel_7('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27797,c_52])).

tff(c_28932,plain,(
    ! [C_1134,A_1135,B_1136,D_1137] :
      ( r2_hidden(C_1134,k2_pre_topc(A_1135,B_1136))
      | ~ r1_waybel_7(A_1135,D_1137,C_1134)
      | ~ r2_hidden(B_1136,D_1137)
      | ~ m1_subset_1(D_1137,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_1135)))))
      | ~ v13_waybel_0(D_1137,k3_yellow_1(k2_struct_0(A_1135)))
      | ~ v2_waybel_0(D_1137,k3_yellow_1(k2_struct_0(A_1135)))
      | ~ v1_subset_1(D_1137,u1_struct_0(k3_yellow_1(k2_struct_0(A_1135))))
      | v1_xboole_0(D_1137)
      | ~ m1_subset_1(C_1134,u1_struct_0(A_1135))
      | ~ m1_subset_1(B_1136,k1_zfmisc_1(u1_struct_0(A_1135)))
      | ~ l1_pre_topc(A_1135)
      | ~ v2_pre_topc(A_1135)
      | v2_struct_0(A_1135) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28938,plain,(
    ! [B_1136] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1136))
      | ~ r2_hidden(B_1136,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_27810,c_28932])).

tff(c_28946,plain,(
    ! [B_1136] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1136))
      | ~ r2_hidden(B_1136,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_1136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_27808,c_27849,c_27822,c_27813,c_27890,c_28938])).

tff(c_28949,plain,(
    ! [B_1139] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1139))
      | ~ r2_hidden(B_1139,'#skF_5')
      | ~ m1_subset_1(B_1139,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_27796,c_28946])).

tff(c_28956,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_28949])).

tff(c_28962,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27800,c_27978,c_28956])).

tff(c_28964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27806,c_28962])).

%------------------------------------------------------------------------------
