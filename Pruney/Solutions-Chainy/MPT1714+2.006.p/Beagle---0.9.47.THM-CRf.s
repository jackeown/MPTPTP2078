%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 10.22s
% Output     : CNFRefutation 10.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 338 expanded)
%              Number of leaves         :   27 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  248 (1396 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_134,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20267,plain,(
    ! [B_676,A_677] :
      ( l1_pre_topc(B_676)
      | ~ m1_pre_topc(B_676,A_677)
      | ~ l1_pre_topc(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20279,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_20267])).

tff(c_20289,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20279])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20286,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_20267])).

tff(c_20290,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20286])).

tff(c_20292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20289,c_20290])).

tff(c_20294,plain,(
    l1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_20286])).

tff(c_20,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20270,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_20267])).

tff(c_20282,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20270])).

tff(c_20036,plain,(
    ! [B_636,A_637] :
      ( l1_pre_topc(B_636)
      | ~ m1_pre_topc(B_636,A_637)
      | ~ l1_pre_topc(A_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20039,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_20036])).

tff(c_20051,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20039])).

tff(c_48,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20042,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_20036])).

tff(c_20054,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20042])).

tff(c_72,plain,(
    ! [B_48,A_49] :
      ( l1_pre_topc(B_48)
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_90,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_78])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_244,plain,(
    ! [B_77,A_78] :
      ( v2_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_250,plain,
    ( v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_244])).

tff(c_262,plain,(
    v2_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_250])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_799,plain,(
    ! [B_121,C_122,A_123] :
      ( m1_pre_topc(B_121,C_122)
      | ~ r1_tarski(u1_struct_0(B_121),u1_struct_0(C_122))
      | ~ m1_pre_topc(C_122,A_123)
      | ~ m1_pre_topc(B_121,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1240,plain,(
    ! [B_146,A_147] :
      ( m1_pre_topc(B_146,B_146)
      | ~ m1_pre_topc(B_146,A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147) ) ),
    inference(resolution,[status(thm)],[c_8,c_799])).

tff(c_1244,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1240])).

tff(c_1254,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1244])).

tff(c_30,plain,(
    ! [B_26,C_28,A_22] :
      ( r1_tarski(u1_struct_0(B_26),u1_struct_0(C_28))
      | ~ m1_pre_topc(B_26,C_28)
      | ~ m1_pre_topc(C_28,A_22)
      | ~ m1_pre_topc(B_26,A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1286,plain,(
    ! [B_26] :
      ( r1_tarski(u1_struct_0(B_26),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_26,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1254,c_30])).

tff(c_1298,plain,(
    ! [B_26] :
      ( r1_tarski(u1_struct_0(B_26),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_26,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_90,c_1286])).

tff(c_428,plain,(
    ! [A_91,B_92] :
      ( r1_xboole_0(u1_struct_0(A_91),u1_struct_0(B_92))
      | ~ r1_tsep_1(A_91,B_92)
      | ~ l1_struct_0(B_92)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2730,plain,(
    ! [A_203,B_204] :
      ( k4_xboole_0(u1_struct_0(A_203),u1_struct_0(B_204)) = u1_struct_0(A_203)
      | ~ r1_tsep_1(A_203,B_204)
      | ~ l1_struct_0(B_204)
      | ~ l1_struct_0(A_203) ) ),
    inference(resolution,[status(thm)],[c_428,c_14])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5190,plain,(
    ! [A_280,B_281,A_282] :
      ( r1_xboole_0(A_280,u1_struct_0(B_281))
      | ~ r1_tarski(A_280,u1_struct_0(A_282))
      | ~ r1_tsep_1(A_282,B_281)
      | ~ l1_struct_0(B_281)
      | ~ l1_struct_0(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2730,c_10])).

tff(c_5219,plain,(
    ! [B_26,B_281] :
      ( r1_xboole_0(u1_struct_0(B_26),u1_struct_0(B_281))
      | ~ r1_tsep_1('#skF_2',B_281)
      | ~ l1_struct_0(B_281)
      | ~ l1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_26,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1298,c_5190])).

tff(c_5268,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5219])).

tff(c_5271,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_5268])).

tff(c_5275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5271])).

tff(c_5277,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5219])).

tff(c_75,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_75])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_94,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84])).

tff(c_34,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_397,plain,(
    ! [B_89,A_90] :
      ( r1_tsep_1(B_89,A_90)
      | ~ r1_tsep_1(A_90,B_89)
      | ~ l1_struct_0(B_89)
      | ~ l1_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_400,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_397])).

tff(c_401,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_404,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_401])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_404])).

tff(c_409,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_411,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_414,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_414])).

tff(c_420,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_410,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_256,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_244])).

tff(c_268,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_256])).

tff(c_1248,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1240])).

tff(c_1260,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1248])).

tff(c_1309,plain,(
    ! [B_26] :
      ( r1_tarski(u1_struct_0(B_26),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_26,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1260,c_30])).

tff(c_1321,plain,(
    ! [B_26] :
      ( r1_tarski(u1_struct_0(B_26),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_26,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_94,c_1309])).

tff(c_5195,plain,(
    ! [B_26,B_281] :
      ( r1_xboole_0(u1_struct_0(B_26),u1_struct_0(B_281))
      | ~ r1_tsep_1('#skF_3',B_281)
      | ~ l1_struct_0(B_281)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1321,c_5190])).

tff(c_10683,plain,(
    ! [B_415,B_416] :
      ( r1_xboole_0(u1_struct_0(B_415),u1_struct_0(B_416))
      | ~ r1_tsep_1('#skF_3',B_416)
      | ~ l1_struct_0(B_416)
      | ~ m1_pre_topc(B_415,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_5195])).

tff(c_24,plain,(
    ! [A_17,B_19] :
      ( r1_tsep_1(A_17,B_19)
      | ~ r1_xboole_0(u1_struct_0(A_17),u1_struct_0(B_19))
      | ~ l1_struct_0(B_19)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19996,plain,(
    ! [B_631,B_632] :
      ( r1_tsep_1(B_631,B_632)
      | ~ l1_struct_0(B_631)
      | ~ r1_tsep_1('#skF_3',B_632)
      | ~ l1_struct_0(B_632)
      | ~ m1_pre_topc(B_631,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10683,c_24])).

tff(c_20003,plain,(
    ! [B_631] :
      ( r1_tsep_1(B_631,'#skF_4')
      | ~ l1_struct_0(B_631)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_631,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_19996])).

tff(c_20011,plain,(
    ! [B_633] :
      ( r1_tsep_1(B_633,'#skF_4')
      | ~ l1_struct_0(B_633)
      | ~ m1_pre_topc(B_633,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_20003])).

tff(c_36,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_61,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_20021,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20011,c_61])).

tff(c_20032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5277,c_20021])).

tff(c_20033,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_20034,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_20227,plain,(
    ! [B_668,A_669] :
      ( r1_tsep_1(B_668,A_669)
      | ~ r1_tsep_1(A_669,B_668)
      | ~ l1_struct_0(B_668)
      | ~ l1_struct_0(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20229,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20034,c_20227])).

tff(c_20234,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20033,c_20229])).

tff(c_20236,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20234])).

tff(c_20239,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_20236])).

tff(c_20243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20054,c_20239])).

tff(c_20244,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_20234])).

tff(c_20249,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_20244])).

tff(c_20253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20051,c_20249])).

tff(c_20255,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_20254,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_20471,plain,(
    ! [B_707,A_708] :
      ( r1_tsep_1(B_707,A_708)
      | ~ r1_tsep_1(A_708,B_707)
      | ~ l1_struct_0(B_707)
      | ~ l1_struct_0(A_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20473,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20254,c_20471])).

tff(c_20476,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20255,c_20473])).

tff(c_20477,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20476])).

tff(c_20480,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_20477])).

tff(c_20484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20282,c_20480])).

tff(c_20485,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_20476])).

tff(c_20489,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_20485])).

tff(c_20493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20294,c_20489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:10:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.22/4.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.22/4.22  
% 10.22/4.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.22/4.22  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.22/4.22  
% 10.22/4.22  %Foreground sorts:
% 10.22/4.22  
% 10.22/4.22  
% 10.22/4.22  %Background operators:
% 10.22/4.22  
% 10.22/4.22  
% 10.22/4.22  %Foreground operators:
% 10.22/4.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.22/4.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.22/4.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.22/4.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.22/4.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.22/4.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.22/4.22  tff('#skF_2', type, '#skF_2': $i).
% 10.22/4.22  tff('#skF_3', type, '#skF_3': $i).
% 10.22/4.22  tff('#skF_1', type, '#skF_1': $i).
% 10.22/4.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.22/4.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.22/4.22  tff('#skF_4', type, '#skF_4': $i).
% 10.22/4.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.22/4.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.22/4.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.22/4.22  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 10.22/4.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.22/4.22  
% 10.22/4.24  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 10.22/4.24  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.22/4.24  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.22/4.24  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 10.22/4.24  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.22/4.24  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 10.22/4.24  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 10.22/4.24  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.22/4.24  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 10.22/4.24  tff(f_82, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 10.22/4.24  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_20267, plain, (![B_676, A_677]: (l1_pre_topc(B_676) | ~m1_pre_topc(B_676, A_677) | ~l1_pre_topc(A_677))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.22/4.24  tff(c_20279, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_20267])).
% 10.22/4.24  tff(c_20289, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20279])).
% 10.22/4.24  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_20286, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_20267])).
% 10.22/4.24  tff(c_20290, plain, (~l1_pre_topc('#skF_3')), inference(splitLeft, [status(thm)], [c_20286])).
% 10.22/4.24  tff(c_20292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20289, c_20290])).
% 10.22/4.24  tff(c_20294, plain, (l1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_20286])).
% 10.22/4.24  tff(c_20, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.22/4.24  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_20270, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_20267])).
% 10.22/4.24  tff(c_20282, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20270])).
% 10.22/4.24  tff(c_20036, plain, (![B_636, A_637]: (l1_pre_topc(B_636) | ~m1_pre_topc(B_636, A_637) | ~l1_pre_topc(A_637))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.22/4.24  tff(c_20039, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_20036])).
% 10.22/4.24  tff(c_20051, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20039])).
% 10.22/4.24  tff(c_48, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_20042, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_20036])).
% 10.22/4.24  tff(c_20054, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20042])).
% 10.22/4.24  tff(c_72, plain, (![B_48, A_49]: (l1_pre_topc(B_48) | ~m1_pre_topc(B_48, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.22/4.24  tff(c_78, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_72])).
% 10.22/4.24  tff(c_90, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_78])).
% 10.22/4.24  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_244, plain, (![B_77, A_78]: (v2_pre_topc(B_77) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.22/4.24  tff(c_250, plain, (v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_244])).
% 10.22/4.24  tff(c_262, plain, (v2_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_250])).
% 10.22/4.24  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.22/4.24  tff(c_799, plain, (![B_121, C_122, A_123]: (m1_pre_topc(B_121, C_122) | ~r1_tarski(u1_struct_0(B_121), u1_struct_0(C_122)) | ~m1_pre_topc(C_122, A_123) | ~m1_pre_topc(B_121, A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.22/4.24  tff(c_1240, plain, (![B_146, A_147]: (m1_pre_topc(B_146, B_146) | ~m1_pre_topc(B_146, A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147))), inference(resolution, [status(thm)], [c_8, c_799])).
% 10.22/4.24  tff(c_1244, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1240])).
% 10.22/4.24  tff(c_1254, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1244])).
% 10.22/4.24  tff(c_30, plain, (![B_26, C_28, A_22]: (r1_tarski(u1_struct_0(B_26), u1_struct_0(C_28)) | ~m1_pre_topc(B_26, C_28) | ~m1_pre_topc(C_28, A_22) | ~m1_pre_topc(B_26, A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.22/4.24  tff(c_1286, plain, (![B_26]: (r1_tarski(u1_struct_0(B_26), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_26, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1254, c_30])).
% 10.22/4.24  tff(c_1298, plain, (![B_26]: (r1_tarski(u1_struct_0(B_26), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_26, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_90, c_1286])).
% 10.22/4.24  tff(c_428, plain, (![A_91, B_92]: (r1_xboole_0(u1_struct_0(A_91), u1_struct_0(B_92)) | ~r1_tsep_1(A_91, B_92) | ~l1_struct_0(B_92) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.22/4.24  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.22/4.24  tff(c_2730, plain, (![A_203, B_204]: (k4_xboole_0(u1_struct_0(A_203), u1_struct_0(B_204))=u1_struct_0(A_203) | ~r1_tsep_1(A_203, B_204) | ~l1_struct_0(B_204) | ~l1_struct_0(A_203))), inference(resolution, [status(thm)], [c_428, c_14])).
% 10.22/4.24  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.22/4.24  tff(c_5190, plain, (![A_280, B_281, A_282]: (r1_xboole_0(A_280, u1_struct_0(B_281)) | ~r1_tarski(A_280, u1_struct_0(A_282)) | ~r1_tsep_1(A_282, B_281) | ~l1_struct_0(B_281) | ~l1_struct_0(A_282))), inference(superposition, [status(thm), theory('equality')], [c_2730, c_10])).
% 10.22/4.24  tff(c_5219, plain, (![B_26, B_281]: (r1_xboole_0(u1_struct_0(B_26), u1_struct_0(B_281)) | ~r1_tsep_1('#skF_2', B_281) | ~l1_struct_0(B_281) | ~l1_struct_0('#skF_2') | ~m1_pre_topc(B_26, '#skF_2'))), inference(resolution, [status(thm)], [c_1298, c_5190])).
% 10.22/4.24  tff(c_5268, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5219])).
% 10.22/4.24  tff(c_5271, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_5268])).
% 10.22/4.24  tff(c_5275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_5271])).
% 10.22/4.24  tff(c_5277, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_5219])).
% 10.22/4.24  tff(c_75, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_72])).
% 10.22/4.24  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_75])).
% 10.22/4.24  tff(c_84, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_72])).
% 10.22/4.24  tff(c_94, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84])).
% 10.22/4.24  tff(c_34, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_60, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 10.22/4.24  tff(c_397, plain, (![B_89, A_90]: (r1_tsep_1(B_89, A_90) | ~r1_tsep_1(A_90, B_89) | ~l1_struct_0(B_89) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.22/4.24  tff(c_400, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_397])).
% 10.22/4.24  tff(c_401, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_400])).
% 10.22/4.24  tff(c_404, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_401])).
% 10.22/4.24  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_404])).
% 10.22/4.24  tff(c_409, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_400])).
% 10.22/4.24  tff(c_411, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_409])).
% 10.22/4.24  tff(c_414, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_411])).
% 10.22/4.24  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_414])).
% 10.22/4.24  tff(c_420, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_409])).
% 10.22/4.24  tff(c_410, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_400])).
% 10.22/4.24  tff(c_256, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_244])).
% 10.22/4.24  tff(c_268, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_256])).
% 10.22/4.24  tff(c_1248, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1240])).
% 10.22/4.24  tff(c_1260, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1248])).
% 10.22/4.24  tff(c_1309, plain, (![B_26]: (r1_tarski(u1_struct_0(B_26), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_26, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_1260, c_30])).
% 10.22/4.24  tff(c_1321, plain, (![B_26]: (r1_tarski(u1_struct_0(B_26), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_26, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_94, c_1309])).
% 10.22/4.24  tff(c_5195, plain, (![B_26, B_281]: (r1_xboole_0(u1_struct_0(B_26), u1_struct_0(B_281)) | ~r1_tsep_1('#skF_3', B_281) | ~l1_struct_0(B_281) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_26, '#skF_3'))), inference(resolution, [status(thm)], [c_1321, c_5190])).
% 10.22/4.24  tff(c_10683, plain, (![B_415, B_416]: (r1_xboole_0(u1_struct_0(B_415), u1_struct_0(B_416)) | ~r1_tsep_1('#skF_3', B_416) | ~l1_struct_0(B_416) | ~m1_pre_topc(B_415, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_410, c_5195])).
% 10.22/4.24  tff(c_24, plain, (![A_17, B_19]: (r1_tsep_1(A_17, B_19) | ~r1_xboole_0(u1_struct_0(A_17), u1_struct_0(B_19)) | ~l1_struct_0(B_19) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.22/4.24  tff(c_19996, plain, (![B_631, B_632]: (r1_tsep_1(B_631, B_632) | ~l1_struct_0(B_631) | ~r1_tsep_1('#skF_3', B_632) | ~l1_struct_0(B_632) | ~m1_pre_topc(B_631, '#skF_3'))), inference(resolution, [status(thm)], [c_10683, c_24])).
% 10.22/4.24  tff(c_20003, plain, (![B_631]: (r1_tsep_1(B_631, '#skF_4') | ~l1_struct_0(B_631) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_631, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_19996])).
% 10.22/4.24  tff(c_20011, plain, (![B_633]: (r1_tsep_1(B_633, '#skF_4') | ~l1_struct_0(B_633) | ~m1_pre_topc(B_633, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_20003])).
% 10.22/4.24  tff(c_36, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.22/4.24  tff(c_61, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 10.22/4.24  tff(c_20021, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20011, c_61])).
% 10.22/4.24  tff(c_20032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_5277, c_20021])).
% 10.22/4.24  tff(c_20033, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 10.22/4.24  tff(c_20034, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 10.22/4.24  tff(c_20227, plain, (![B_668, A_669]: (r1_tsep_1(B_668, A_669) | ~r1_tsep_1(A_669, B_668) | ~l1_struct_0(B_668) | ~l1_struct_0(A_669))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.22/4.24  tff(c_20229, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20034, c_20227])).
% 10.22/4.24  tff(c_20234, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20033, c_20229])).
% 10.22/4.24  tff(c_20236, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_20234])).
% 10.22/4.24  tff(c_20239, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_20236])).
% 10.22/4.24  tff(c_20243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20054, c_20239])).
% 10.22/4.24  tff(c_20244, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_20234])).
% 10.22/4.24  tff(c_20249, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_20244])).
% 10.22/4.24  tff(c_20253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20051, c_20249])).
% 10.22/4.24  tff(c_20255, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 10.22/4.24  tff(c_20254, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 10.22/4.24  tff(c_20471, plain, (![B_707, A_708]: (r1_tsep_1(B_707, A_708) | ~r1_tsep_1(A_708, B_707) | ~l1_struct_0(B_707) | ~l1_struct_0(A_708))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.22/4.24  tff(c_20473, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_20254, c_20471])).
% 10.22/4.24  tff(c_20476, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20255, c_20473])).
% 10.22/4.24  tff(c_20477, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_20476])).
% 10.22/4.24  tff(c_20480, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_20477])).
% 10.22/4.24  tff(c_20484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20282, c_20480])).
% 10.22/4.24  tff(c_20485, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_20476])).
% 10.22/4.24  tff(c_20489, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_20485])).
% 10.22/4.24  tff(c_20493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20294, c_20489])).
% 10.22/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.22/4.24  
% 10.22/4.24  Inference rules
% 10.22/4.24  ----------------------
% 10.22/4.24  #Ref     : 0
% 10.22/4.24  #Sup     : 5667
% 10.22/4.24  #Fact    : 0
% 10.22/4.24  #Define  : 0
% 10.22/4.24  #Split   : 13
% 10.22/4.24  #Chain   : 0
% 10.22/4.24  #Close   : 0
% 10.22/4.24  
% 10.22/4.24  Ordering : KBO
% 10.22/4.24  
% 10.22/4.24  Simplification rules
% 10.22/4.24  ----------------------
% 10.22/4.24  #Subsume      : 1508
% 10.22/4.24  #Demod        : 1985
% 10.22/4.24  #Tautology    : 1837
% 10.22/4.24  #SimpNegUnit  : 2
% 10.22/4.24  #BackRed      : 0
% 10.22/4.24  
% 10.22/4.24  #Partial instantiations: 0
% 10.22/4.24  #Strategies tried      : 1
% 10.22/4.24  
% 10.22/4.24  Timing (in seconds)
% 10.22/4.24  ----------------------
% 10.22/4.24  Preprocessing        : 0.36
% 10.22/4.24  Parsing              : 0.19
% 10.22/4.24  CNF conversion       : 0.03
% 10.22/4.24  Main loop            : 3.03
% 10.22/4.24  Inferencing          : 0.72
% 10.22/4.24  Reduction            : 1.02
% 10.22/4.24  Demodulation         : 0.82
% 10.22/4.24  BG Simplification    : 0.09
% 10.22/4.24  Subsumption          : 1.02
% 10.22/4.24  Abstraction          : 0.12
% 10.22/4.24  MUC search           : 0.00
% 10.22/4.24  Cooper               : 0.00
% 10.22/4.24  Total                : 3.43
% 10.22/4.24  Index Insertion      : 0.00
% 10.22/4.24  Index Deletion       : 0.00
% 10.22/4.24  Index Matching       : 0.00
% 10.22/4.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
