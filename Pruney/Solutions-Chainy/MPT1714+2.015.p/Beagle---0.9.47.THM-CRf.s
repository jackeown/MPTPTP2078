%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:34 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 264 expanded)
%              Number of leaves         :   32 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  216 (1027 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_146,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_108,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1490,plain,(
    ! [B_267,A_268] :
      ( l1_pre_topc(B_267)
      | ~ m1_pre_topc(B_267,A_268)
      | ~ l1_pre_topc(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1496,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1490])).

tff(c_1508,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1496])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1493,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1490])).

tff(c_1505,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1493])).

tff(c_1306,plain,(
    ! [B_235,A_236] :
      ( l1_pre_topc(B_235)
      | ~ m1_pre_topc(B_235,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1309,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1306])).

tff(c_1321,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1309])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1315,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1306])).

tff(c_1327,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1315])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_100,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_121,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_109])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_371,plain,(
    ! [B_111,C_112,A_113] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0(C_112))
      | ~ m1_pre_topc(B_111,C_112)
      | ~ m1_pre_topc(C_112,A_113)
      | ~ m1_pre_topc(B_111,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_377,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_111,'#skF_4')
      | ~ m1_pre_topc(B_111,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_371])).

tff(c_388,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_111,'#skF_4')
      | ~ m1_pre_topc(B_111,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_377])).

tff(c_343,plain,(
    ! [A_100,B_101] :
      ( r1_xboole_0(u1_struct_0(A_100),u1_struct_0(B_101))
      | ~ r1_tsep_1(A_100,B_101)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_605,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(u1_struct_0(A_166),u1_struct_0(B_167)) = u1_struct_0(A_166)
      | ~ r1_tsep_1(A_166,B_167)
      | ~ l1_struct_0(B_167)
      | ~ l1_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_343,c_16])).

tff(c_20,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_650,plain,(
    ! [A_173,A_174,B_175] :
      ( r1_xboole_0(A_173,u1_struct_0(A_174))
      | ~ r1_tarski(A_173,u1_struct_0(B_175))
      | ~ r1_tsep_1(A_174,B_175)
      | ~ l1_struct_0(B_175)
      | ~ l1_struct_0(A_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_20])).

tff(c_657,plain,(
    ! [B_111,A_174] :
      ( r1_xboole_0(u1_struct_0(B_111),u1_struct_0(A_174))
      | ~ r1_tsep_1(A_174,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(A_174)
      | ~ m1_pre_topc(B_111,'#skF_4')
      | ~ m1_pre_topc(B_111,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_388,c_650])).

tff(c_1207,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_1210,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1207])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1210])).

tff(c_1216,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_103,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_100])).

tff(c_115,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_103])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_118,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_106])).

tff(c_38,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_79,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_279,plain,(
    ! [B_95,A_96] :
      ( r1_tsep_1(B_95,A_96)
      | ~ r1_tsep_1(A_96,B_95)
      | ~ l1_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_282,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_79,c_279])).

tff(c_283,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_286,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_283])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_286])).

tff(c_291,plain,
    ( ~ l1_struct_0('#skF_6')
    | r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_293,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_296,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_293])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_296])).

tff(c_302,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_301,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_292,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_375,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_111,'#skF_5')
      | ~ m1_pre_topc(B_111,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_371])).

tff(c_385,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_111,'#skF_5')
      | ~ m1_pre_topc(B_111,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_375])).

tff(c_654,plain,(
    ! [B_111,A_174] :
      ( r1_xboole_0(u1_struct_0(B_111),u1_struct_0(A_174))
      | ~ r1_tsep_1(A_174,'#skF_5')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0(A_174)
      | ~ m1_pre_topc(B_111,'#skF_5')
      | ~ m1_pre_topc(B_111,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_385,c_650])).

tff(c_1182,plain,(
    ! [B_220,A_221] :
      ( r1_xboole_0(u1_struct_0(B_220),u1_struct_0(A_221))
      | ~ r1_tsep_1(A_221,'#skF_5')
      | ~ l1_struct_0(A_221)
      | ~ m1_pre_topc(B_220,'#skF_5')
      | ~ m1_pre_topc(B_220,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_654])).

tff(c_28,plain,(
    ! [A_24,B_26] :
      ( r1_tsep_1(A_24,B_26)
      | ~ r1_xboole_0(u1_struct_0(A_24),u1_struct_0(B_26))
      | ~ l1_struct_0(B_26)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1280,plain,(
    ! [B_230,A_231] :
      ( r1_tsep_1(B_230,A_231)
      | ~ l1_struct_0(B_230)
      | ~ r1_tsep_1(A_231,'#skF_5')
      | ~ l1_struct_0(A_231)
      | ~ m1_pre_topc(B_230,'#skF_5')
      | ~ m1_pre_topc(B_230,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1182,c_28])).

tff(c_1282,plain,(
    ! [B_230] :
      ( r1_tsep_1(B_230,'#skF_6')
      | ~ l1_struct_0(B_230)
      | ~ l1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_230,'#skF_5')
      | ~ m1_pre_topc(B_230,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_301,c_1280])).

tff(c_1286,plain,(
    ! [B_232] :
      ( r1_tsep_1(B_232,'#skF_6')
      | ~ l1_struct_0(B_232)
      | ~ m1_pre_topc(B_232,'#skF_5')
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_1282])).

tff(c_40,plain,
    ( ~ r1_tsep_1('#skF_6','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_80,plain,(
    ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_1291,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1286,c_80])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42,c_1216,c_1291])).

tff(c_1299,plain,(
    ~ r1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1300,plain,(
    r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1460,plain,(
    ! [B_265,A_266] :
      ( r1_tsep_1(B_265,A_266)
      | ~ r1_tsep_1(A_266,B_265)
      | ~ l1_struct_0(B_265)
      | ~ l1_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1462,plain,
    ( r1_tsep_1('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1300,c_1460])).

tff(c_1467,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1299,c_1462])).

tff(c_1469,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1467])).

tff(c_1472,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1469])).

tff(c_1476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1327,c_1472])).

tff(c_1477,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1467])).

tff(c_1482,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_1477])).

tff(c_1486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1482])).

tff(c_1488,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1487,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1688,plain,(
    ! [B_307,A_308] :
      ( r1_tsep_1(B_307,A_308)
      | ~ r1_tsep_1(A_308,B_307)
      | ~ l1_struct_0(B_307)
      | ~ l1_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1690,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1487,c_1688])).

tff(c_1693,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1488,c_1690])).

tff(c_1694,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1693])).

tff(c_1697,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_1694])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_1697])).

tff(c_1702,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_1706,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1702])).

tff(c_1710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_1706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:08:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.61  
% 3.86/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.61  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.86/1.61  
% 3.86/1.61  %Foreground sorts:
% 3.86/1.61  
% 3.86/1.61  
% 3.86/1.61  %Background operators:
% 3.86/1.61  
% 3.86/1.61  
% 3.86/1.61  %Foreground operators:
% 3.86/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.86/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.86/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.86/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.86/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.86/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.86/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.86/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.86/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.86/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.86/1.61  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.86/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.61  
% 3.86/1.62  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.86/1.62  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.86/1.62  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.86/1.62  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.86/1.62  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.86/1.62  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.86/1.62  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.86/1.62  tff(f_94, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.86/1.62  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_1490, plain, (![B_267, A_268]: (l1_pre_topc(B_267) | ~m1_pre_topc(B_267, A_268) | ~l1_pre_topc(A_268))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.62  tff(c_1496, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1490])).
% 3.86/1.62  tff(c_1508, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1496])).
% 3.86/1.62  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.86/1.62  tff(c_44, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_1493, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1490])).
% 3.86/1.62  tff(c_1505, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1493])).
% 3.86/1.62  tff(c_1306, plain, (![B_235, A_236]: (l1_pre_topc(B_235) | ~m1_pre_topc(B_235, A_236) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.62  tff(c_1309, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1306])).
% 3.86/1.62  tff(c_1321, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1309])).
% 3.86/1.62  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_1315, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1306])).
% 3.86/1.62  tff(c_1327, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1315])).
% 3.86/1.62  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_100, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.62  tff(c_109, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_100])).
% 3.86/1.62  tff(c_121, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_109])).
% 3.86/1.62  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_371, plain, (![B_111, C_112, A_113]: (r1_tarski(u1_struct_0(B_111), u1_struct_0(C_112)) | ~m1_pre_topc(B_111, C_112) | ~m1_pre_topc(C_112, A_113) | ~m1_pre_topc(B_111, A_113) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.86/1.62  tff(c_377, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_111, '#skF_4') | ~m1_pre_topc(B_111, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_371])).
% 3.86/1.62  tff(c_388, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_111, '#skF_4') | ~m1_pre_topc(B_111, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_377])).
% 3.86/1.62  tff(c_343, plain, (![A_100, B_101]: (r1_xboole_0(u1_struct_0(A_100), u1_struct_0(B_101)) | ~r1_tsep_1(A_100, B_101) | ~l1_struct_0(B_101) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.86/1.62  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.62  tff(c_605, plain, (![A_166, B_167]: (k4_xboole_0(u1_struct_0(A_166), u1_struct_0(B_167))=u1_struct_0(A_166) | ~r1_tsep_1(A_166, B_167) | ~l1_struct_0(B_167) | ~l1_struct_0(A_166))), inference(resolution, [status(thm)], [c_343, c_16])).
% 3.86/1.62  tff(c_20, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.86/1.62  tff(c_650, plain, (![A_173, A_174, B_175]: (r1_xboole_0(A_173, u1_struct_0(A_174)) | ~r1_tarski(A_173, u1_struct_0(B_175)) | ~r1_tsep_1(A_174, B_175) | ~l1_struct_0(B_175) | ~l1_struct_0(A_174))), inference(superposition, [status(thm), theory('equality')], [c_605, c_20])).
% 3.86/1.62  tff(c_657, plain, (![B_111, A_174]: (r1_xboole_0(u1_struct_0(B_111), u1_struct_0(A_174)) | ~r1_tsep_1(A_174, '#skF_4') | ~l1_struct_0('#skF_4') | ~l1_struct_0(A_174) | ~m1_pre_topc(B_111, '#skF_4') | ~m1_pre_topc(B_111, '#skF_3'))), inference(resolution, [status(thm)], [c_388, c_650])).
% 3.86/1.62  tff(c_1207, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_657])).
% 3.86/1.62  tff(c_1210, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1207])).
% 3.86/1.62  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_1210])).
% 3.86/1.62  tff(c_1216, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_657])).
% 3.86/1.62  tff(c_103, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_100])).
% 3.86/1.62  tff(c_115, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_103])).
% 3.86/1.62  tff(c_106, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_100])).
% 3.86/1.62  tff(c_118, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_106])).
% 3.86/1.62  tff(c_38, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_79, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_38])).
% 3.86/1.62  tff(c_279, plain, (![B_95, A_96]: (r1_tsep_1(B_95, A_96) | ~r1_tsep_1(A_96, B_95) | ~l1_struct_0(B_95) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.86/1.62  tff(c_282, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_79, c_279])).
% 3.86/1.62  tff(c_283, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_282])).
% 3.86/1.62  tff(c_286, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_283])).
% 3.86/1.62  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_286])).
% 3.86/1.62  tff(c_291, plain, (~l1_struct_0('#skF_6') | r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_282])).
% 3.86/1.62  tff(c_293, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_291])).
% 3.86/1.62  tff(c_296, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_24, c_293])).
% 3.86/1.62  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_296])).
% 3.86/1.62  tff(c_302, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_291])).
% 3.86/1.62  tff(c_301, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_291])).
% 3.86/1.62  tff(c_292, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_282])).
% 3.86/1.62  tff(c_375, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_111, '#skF_5') | ~m1_pre_topc(B_111, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_371])).
% 3.86/1.62  tff(c_385, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_111, '#skF_5') | ~m1_pre_topc(B_111, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_375])).
% 3.86/1.62  tff(c_654, plain, (![B_111, A_174]: (r1_xboole_0(u1_struct_0(B_111), u1_struct_0(A_174)) | ~r1_tsep_1(A_174, '#skF_5') | ~l1_struct_0('#skF_5') | ~l1_struct_0(A_174) | ~m1_pre_topc(B_111, '#skF_5') | ~m1_pre_topc(B_111, '#skF_3'))), inference(resolution, [status(thm)], [c_385, c_650])).
% 3.86/1.62  tff(c_1182, plain, (![B_220, A_221]: (r1_xboole_0(u1_struct_0(B_220), u1_struct_0(A_221)) | ~r1_tsep_1(A_221, '#skF_5') | ~l1_struct_0(A_221) | ~m1_pre_topc(B_220, '#skF_5') | ~m1_pre_topc(B_220, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_654])).
% 3.86/1.62  tff(c_28, plain, (![A_24, B_26]: (r1_tsep_1(A_24, B_26) | ~r1_xboole_0(u1_struct_0(A_24), u1_struct_0(B_26)) | ~l1_struct_0(B_26) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.86/1.62  tff(c_1280, plain, (![B_230, A_231]: (r1_tsep_1(B_230, A_231) | ~l1_struct_0(B_230) | ~r1_tsep_1(A_231, '#skF_5') | ~l1_struct_0(A_231) | ~m1_pre_topc(B_230, '#skF_5') | ~m1_pre_topc(B_230, '#skF_3'))), inference(resolution, [status(thm)], [c_1182, c_28])).
% 3.86/1.62  tff(c_1282, plain, (![B_230]: (r1_tsep_1(B_230, '#skF_6') | ~l1_struct_0(B_230) | ~l1_struct_0('#skF_6') | ~m1_pre_topc(B_230, '#skF_5') | ~m1_pre_topc(B_230, '#skF_3'))), inference(resolution, [status(thm)], [c_301, c_1280])).
% 3.86/1.62  tff(c_1286, plain, (![B_232]: (r1_tsep_1(B_232, '#skF_6') | ~l1_struct_0(B_232) | ~m1_pre_topc(B_232, '#skF_5') | ~m1_pre_topc(B_232, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_1282])).
% 3.86/1.62  tff(c_40, plain, (~r1_tsep_1('#skF_6', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.86/1.62  tff(c_80, plain, (~r1_tsep_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 3.86/1.62  tff(c_1291, plain, (~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1286, c_80])).
% 3.86/1.62  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_42, c_1216, c_1291])).
% 3.86/1.62  tff(c_1299, plain, (~r1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 3.86/1.63  tff(c_1300, plain, (r1_tsep_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 3.86/1.63  tff(c_1460, plain, (![B_265, A_266]: (r1_tsep_1(B_265, A_266) | ~r1_tsep_1(A_266, B_265) | ~l1_struct_0(B_265) | ~l1_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.86/1.63  tff(c_1462, plain, (r1_tsep_1('#skF_6', '#skF_4') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1300, c_1460])).
% 3.86/1.63  tff(c_1467, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1299, c_1462])).
% 3.86/1.63  tff(c_1469, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1467])).
% 3.86/1.63  tff(c_1472, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1469])).
% 3.86/1.63  tff(c_1476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1327, c_1472])).
% 3.86/1.63  tff(c_1477, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1467])).
% 3.86/1.63  tff(c_1482, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_24, c_1477])).
% 3.86/1.63  tff(c_1486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1321, c_1482])).
% 3.86/1.63  tff(c_1488, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 3.86/1.63  tff(c_1487, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 3.86/1.63  tff(c_1688, plain, (![B_307, A_308]: (r1_tsep_1(B_307, A_308) | ~r1_tsep_1(A_308, B_307) | ~l1_struct_0(B_307) | ~l1_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.86/1.63  tff(c_1690, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1487, c_1688])).
% 3.86/1.63  tff(c_1693, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1488, c_1690])).
% 3.86/1.63  tff(c_1694, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1693])).
% 3.86/1.63  tff(c_1697, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_24, c_1694])).
% 3.86/1.63  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1505, c_1697])).
% 3.86/1.63  tff(c_1702, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1693])).
% 3.86/1.63  tff(c_1706, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1702])).
% 3.86/1.63  tff(c_1710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1508, c_1706])).
% 3.86/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.63  
% 3.86/1.63  Inference rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Ref     : 0
% 3.86/1.63  #Sup     : 390
% 3.86/1.63  #Fact    : 0
% 3.86/1.63  #Define  : 0
% 3.86/1.63  #Split   : 10
% 3.86/1.63  #Chain   : 0
% 3.86/1.63  #Close   : 0
% 3.86/1.63  
% 3.86/1.63  Ordering : KBO
% 3.86/1.63  
% 3.86/1.63  Simplification rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Subsume      : 49
% 3.86/1.63  #Demod        : 89
% 3.86/1.63  #Tautology    : 133
% 3.86/1.63  #SimpNegUnit  : 9
% 3.86/1.63  #BackRed      : 0
% 3.86/1.63  
% 3.86/1.63  #Partial instantiations: 0
% 3.86/1.63  #Strategies tried      : 1
% 3.86/1.63  
% 3.86/1.63  Timing (in seconds)
% 3.86/1.63  ----------------------
% 3.86/1.63  Preprocessing        : 0.31
% 3.86/1.63  Parsing              : 0.17
% 3.86/1.63  CNF conversion       : 0.02
% 3.86/1.63  Main loop            : 0.55
% 3.86/1.63  Inferencing          : 0.21
% 3.86/1.63  Reduction            : 0.14
% 3.86/1.63  Demodulation         : 0.09
% 3.86/1.63  BG Simplification    : 0.03
% 3.86/1.63  Subsumption          : 0.11
% 3.86/1.63  Abstraction          : 0.03
% 3.86/1.63  MUC search           : 0.00
% 3.86/1.63  Cooper               : 0.00
% 3.86/1.63  Total                : 0.90
% 3.86/1.63  Index Insertion      : 0.00
% 3.86/1.63  Index Deletion       : 0.00
% 3.86/1.63  Index Matching       : 0.00
% 3.86/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
