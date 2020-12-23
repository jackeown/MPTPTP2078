%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:37 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 234 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 ( 922 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_128,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_555,plain,(
    ! [B_94,A_95] :
      ( l1_pre_topc(B_94)
      | ~ m1_pre_topc(B_94,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_567,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_555])).

tff(c_577,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_567])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_561,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_555])).

tff(c_571,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_561])).

tff(c_466,plain,(
    ! [B_84,A_85] :
      ( l1_pre_topc(B_84)
      | ~ m1_pre_topc(B_84,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_472,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_466])).

tff(c_482,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_472])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_475,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_466])).

tff(c_485,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_475])).

tff(c_54,plain,(
    ! [B_39,A_40] :
      ( l1_pre_topc(B_39)
      | ~ m1_pre_topc(B_39,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_73,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_60])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_66])).

tff(c_28,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_110,plain,(
    ! [B_45,A_46] :
      ( r1_tsep_1(B_45,A_46)
      | ~ r1_tsep_1(A_46,B_45)
      | ~ l1_struct_0(B_45)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_113,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_110])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_119])).

tff(c_124,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_129,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_129])).

tff(c_135,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_125,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_85,plain,(
    ! [B_43,A_44] :
      ( v2_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_109,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [B_55,C_56,A_57] :
      ( m1_pre_topc(B_55,C_56)
      | ~ r1_tarski(u1_struct_0(B_55),u1_struct_0(C_56))
      | ~ m1_pre_topc(C_56,A_57)
      | ~ m1_pre_topc(B_55,A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_177,plain,(
    ! [B_61,A_62] :
      ( m1_pre_topc(B_61,B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_185,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_177])).

tff(c_197,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_185])).

tff(c_22,plain,(
    ! [B_23,C_25,A_19] :
      ( r1_tarski(u1_struct_0(B_23),u1_struct_0(C_25))
      | ~ m1_pre_topc(B_23,C_25)
      | ~ m1_pre_topc(C_25,A_19)
      | ~ m1_pre_topc(B_23,A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_224,plain,(
    ! [B_23] :
      ( r1_tarski(u1_struct_0(B_23),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_23,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_197,c_22])).

tff(c_236,plain,(
    ! [B_23] :
      ( r1_tarski(u1_struct_0(B_23),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_23,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_76,c_224])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( r1_xboole_0(u1_struct_0(A_14),u1_struct_0(B_16))
      | ~ r1_tsep_1(A_14,B_16)
      | ~ l1_struct_0(B_16)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [A_51,C_52,B_53,D_54] :
      ( r1_xboole_0(A_51,C_52)
      | ~ r1_xboole_0(B_53,D_54)
      | ~ r1_tarski(C_52,D_54)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_321,plain,(
    ! [A_68,C_69,B_70,A_71] :
      ( r1_xboole_0(A_68,C_69)
      | ~ r1_tarski(C_69,u1_struct_0(B_70))
      | ~ r1_tarski(A_68,u1_struct_0(A_71))
      | ~ r1_tsep_1(A_71,B_70)
      | ~ l1_struct_0(B_70)
      | ~ l1_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_18,c_147])).

tff(c_399,plain,(
    ! [A_74,B_75,A_76] :
      ( r1_xboole_0(A_74,u1_struct_0(B_75))
      | ~ r1_tarski(A_74,u1_struct_0(A_76))
      | ~ r1_tsep_1(A_76,B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_401,plain,(
    ! [B_23,B_75] :
      ( r1_xboole_0(u1_struct_0(B_23),u1_struct_0(B_75))
      | ~ r1_tsep_1('#skF_3',B_75)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_23,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_236,c_399])).

tff(c_417,plain,(
    ! [B_77,B_78] :
      ( r1_xboole_0(u1_struct_0(B_77),u1_struct_0(B_78))
      | ~ r1_tsep_1('#skF_3',B_78)
      | ~ l1_struct_0(B_78)
      | ~ m1_pre_topc(B_77,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_401])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( r1_tsep_1(A_14,B_16)
      | ~ r1_xboole_0(u1_struct_0(A_14),u1_struct_0(B_16))
      | ~ l1_struct_0(B_16)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_433,plain,(
    ! [B_81,B_82] :
      ( r1_tsep_1(B_81,B_82)
      | ~ l1_struct_0(B_81)
      | ~ r1_tsep_1('#skF_3',B_82)
      | ~ l1_struct_0(B_82)
      | ~ m1_pre_topc(B_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_417,c_16])).

tff(c_435,plain,(
    ! [B_81] :
      ( r1_tsep_1(B_81,'#skF_4')
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_433])).

tff(c_439,plain,(
    ! [B_83] :
      ( r1_tsep_1(B_83,'#skF_4')
      | ~ l1_struct_0(B_83)
      | ~ m1_pre_topc(B_83,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_435])).

tff(c_26,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_53,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_447,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_53])).

tff(c_456,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_447])).

tff(c_459,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_456])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_459])).

tff(c_464,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_465,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_525,plain,(
    ! [B_90,A_91] :
      ( r1_tsep_1(B_90,A_91)
      | ~ r1_tsep_1(A_91,B_90)
      | ~ l1_struct_0(B_90)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_527,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_465,c_525])).

tff(c_532,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_527])).

tff(c_534,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_537,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_534])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_537])).

tff(c_542,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_547,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_542])).

tff(c_551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_547])).

tff(c_553,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_552,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_614,plain,(
    ! [B_100,A_101] :
      ( r1_tsep_1(B_100,A_101)
      | ~ r1_tsep_1(A_101,B_100)
      | ~ l1_struct_0(B_100)
      | ~ l1_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_616,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_552,c_614])).

tff(c_619,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_616])).

tff(c_620,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_624,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_620])).

tff(c_628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_624])).

tff(c_629,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_633,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_629])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.34/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.32  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.34/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.32  
% 2.77/1.34  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 2.77/1.34  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.77/1.34  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.77/1.34  tff(f_76, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.77/1.34  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.77/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.34  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.77/1.34  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.77/1.34  tff(f_39, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.77/1.34  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_555, plain, (![B_94, A_95]: (l1_pre_topc(B_94) | ~m1_pre_topc(B_94, A_95) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.34  tff(c_567, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_555])).
% 2.77/1.34  tff(c_577, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_567])).
% 2.77/1.34  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.77/1.34  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_561, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_555])).
% 2.77/1.34  tff(c_571, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_561])).
% 2.77/1.34  tff(c_466, plain, (![B_84, A_85]: (l1_pre_topc(B_84) | ~m1_pre_topc(B_84, A_85) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.34  tff(c_472, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_466])).
% 2.77/1.34  tff(c_482, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_472])).
% 2.77/1.34  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_475, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_466])).
% 2.77/1.34  tff(c_485, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_475])).
% 2.77/1.34  tff(c_54, plain, (![B_39, A_40]: (l1_pre_topc(B_39) | ~m1_pre_topc(B_39, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.34  tff(c_63, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_54])).
% 2.77/1.34  tff(c_73, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_63])).
% 2.77/1.34  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_60, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_54])).
% 2.77/1.34  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_60])).
% 2.77/1.34  tff(c_66, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_54])).
% 2.77/1.34  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_66])).
% 2.77/1.34  tff(c_28, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_52, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.77/1.34  tff(c_110, plain, (![B_45, A_46]: (r1_tsep_1(B_45, A_46) | ~r1_tsep_1(A_46, B_45) | ~l1_struct_0(B_45) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.34  tff(c_113, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_110])).
% 2.77/1.34  tff(c_116, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_113])).
% 2.77/1.34  tff(c_119, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_116])).
% 2.77/1.34  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_119])).
% 2.77/1.34  tff(c_124, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_113])).
% 2.77/1.34  tff(c_126, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_124])).
% 2.77/1.34  tff(c_129, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_126])).
% 2.77/1.34  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_129])).
% 2.77/1.34  tff(c_135, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_124])).
% 2.77/1.34  tff(c_125, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_113])).
% 2.77/1.34  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_85, plain, (![B_43, A_44]: (v2_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.34  tff(c_97, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_85])).
% 2.77/1.34  tff(c_109, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_97])).
% 2.77/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.34  tff(c_151, plain, (![B_55, C_56, A_57]: (m1_pre_topc(B_55, C_56) | ~r1_tarski(u1_struct_0(B_55), u1_struct_0(C_56)) | ~m1_pre_topc(C_56, A_57) | ~m1_pre_topc(B_55, A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.34  tff(c_177, plain, (![B_61, A_62]: (m1_pre_topc(B_61, B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(resolution, [status(thm)], [c_6, c_151])).
% 2.77/1.34  tff(c_185, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_177])).
% 2.77/1.34  tff(c_197, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_185])).
% 2.77/1.34  tff(c_22, plain, (![B_23, C_25, A_19]: (r1_tarski(u1_struct_0(B_23), u1_struct_0(C_25)) | ~m1_pre_topc(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | ~m1_pre_topc(B_23, A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.34  tff(c_224, plain, (![B_23]: (r1_tarski(u1_struct_0(B_23), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_23, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_197, c_22])).
% 2.77/1.34  tff(c_236, plain, (![B_23]: (r1_tarski(u1_struct_0(B_23), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_23, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_76, c_224])).
% 2.77/1.34  tff(c_18, plain, (![A_14, B_16]: (r1_xboole_0(u1_struct_0(A_14), u1_struct_0(B_16)) | ~r1_tsep_1(A_14, B_16) | ~l1_struct_0(B_16) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.34  tff(c_147, plain, (![A_51, C_52, B_53, D_54]: (r1_xboole_0(A_51, C_52) | ~r1_xboole_0(B_53, D_54) | ~r1_tarski(C_52, D_54) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.34  tff(c_321, plain, (![A_68, C_69, B_70, A_71]: (r1_xboole_0(A_68, C_69) | ~r1_tarski(C_69, u1_struct_0(B_70)) | ~r1_tarski(A_68, u1_struct_0(A_71)) | ~r1_tsep_1(A_71, B_70) | ~l1_struct_0(B_70) | ~l1_struct_0(A_71))), inference(resolution, [status(thm)], [c_18, c_147])).
% 2.77/1.34  tff(c_399, plain, (![A_74, B_75, A_76]: (r1_xboole_0(A_74, u1_struct_0(B_75)) | ~r1_tarski(A_74, u1_struct_0(A_76)) | ~r1_tsep_1(A_76, B_75) | ~l1_struct_0(B_75) | ~l1_struct_0(A_76))), inference(resolution, [status(thm)], [c_6, c_321])).
% 2.77/1.34  tff(c_401, plain, (![B_23, B_75]: (r1_xboole_0(u1_struct_0(B_23), u1_struct_0(B_75)) | ~r1_tsep_1('#skF_3', B_75) | ~l1_struct_0(B_75) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_23, '#skF_3'))), inference(resolution, [status(thm)], [c_236, c_399])).
% 2.77/1.34  tff(c_417, plain, (![B_77, B_78]: (r1_xboole_0(u1_struct_0(B_77), u1_struct_0(B_78)) | ~r1_tsep_1('#skF_3', B_78) | ~l1_struct_0(B_78) | ~m1_pre_topc(B_77, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_401])).
% 2.77/1.34  tff(c_16, plain, (![A_14, B_16]: (r1_tsep_1(A_14, B_16) | ~r1_xboole_0(u1_struct_0(A_14), u1_struct_0(B_16)) | ~l1_struct_0(B_16) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.34  tff(c_433, plain, (![B_81, B_82]: (r1_tsep_1(B_81, B_82) | ~l1_struct_0(B_81) | ~r1_tsep_1('#skF_3', B_82) | ~l1_struct_0(B_82) | ~m1_pre_topc(B_81, '#skF_3'))), inference(resolution, [status(thm)], [c_417, c_16])).
% 2.77/1.34  tff(c_435, plain, (![B_81]: (r1_tsep_1(B_81, '#skF_4') | ~l1_struct_0(B_81) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_81, '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_433])).
% 2.77/1.34  tff(c_439, plain, (![B_83]: (r1_tsep_1(B_83, '#skF_4') | ~l1_struct_0(B_83) | ~m1_pre_topc(B_83, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_435])).
% 2.77/1.34  tff(c_26, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.77/1.34  tff(c_53, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.77/1.34  tff(c_447, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_439, c_53])).
% 2.77/1.34  tff(c_456, plain, (~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_447])).
% 2.77/1.34  tff(c_459, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_456])).
% 2.77/1.34  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_459])).
% 2.77/1.34  tff(c_464, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.77/1.34  tff(c_465, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.77/1.34  tff(c_525, plain, (![B_90, A_91]: (r1_tsep_1(B_90, A_91) | ~r1_tsep_1(A_91, B_90) | ~l1_struct_0(B_90) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.34  tff(c_527, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_465, c_525])).
% 2.77/1.34  tff(c_532, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_464, c_527])).
% 2.77/1.34  tff(c_534, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_532])).
% 2.77/1.34  tff(c_537, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_534])).
% 2.77/1.34  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_537])).
% 2.77/1.34  tff(c_542, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_532])).
% 2.77/1.34  tff(c_547, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_542])).
% 2.77/1.34  tff(c_551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_547])).
% 2.77/1.34  tff(c_553, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.77/1.34  tff(c_552, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.77/1.34  tff(c_614, plain, (![B_100, A_101]: (r1_tsep_1(B_100, A_101) | ~r1_tsep_1(A_101, B_100) | ~l1_struct_0(B_100) | ~l1_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.34  tff(c_616, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_552, c_614])).
% 2.77/1.34  tff(c_619, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_553, c_616])).
% 2.77/1.34  tff(c_620, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_619])).
% 2.77/1.34  tff(c_624, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_620])).
% 2.77/1.34  tff(c_628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_571, c_624])).
% 2.77/1.34  tff(c_629, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_619])).
% 2.77/1.34  tff(c_633, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_629])).
% 2.77/1.34  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_633])).
% 2.77/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.34  
% 2.77/1.34  Inference rules
% 2.77/1.34  ----------------------
% 2.77/1.34  #Ref     : 0
% 2.77/1.34  #Sup     : 98
% 2.77/1.34  #Fact    : 0
% 2.77/1.34  #Define  : 0
% 2.77/1.34  #Split   : 10
% 2.77/1.34  #Chain   : 0
% 2.77/1.34  #Close   : 0
% 2.77/1.34  
% 2.77/1.34  Ordering : KBO
% 2.77/1.34  
% 2.77/1.34  Simplification rules
% 2.77/1.34  ----------------------
% 2.77/1.34  #Subsume      : 10
% 2.77/1.34  #Demod        : 120
% 2.77/1.34  #Tautology    : 32
% 2.77/1.34  #SimpNegUnit  : 2
% 2.77/1.34  #BackRed      : 0
% 2.77/1.34  
% 2.77/1.34  #Partial instantiations: 0
% 2.77/1.34  #Strategies tried      : 1
% 2.77/1.34  
% 2.77/1.34  Timing (in seconds)
% 2.77/1.34  ----------------------
% 2.77/1.35  Preprocessing        : 0.29
% 2.77/1.35  Parsing              : 0.16
% 2.77/1.35  CNF conversion       : 0.02
% 2.77/1.35  Main loop            : 0.30
% 2.77/1.35  Inferencing          : 0.11
% 2.77/1.35  Reduction            : 0.09
% 2.77/1.35  Demodulation         : 0.06
% 2.77/1.35  BG Simplification    : 0.02
% 2.77/1.35  Subsumption          : 0.06
% 2.77/1.35  Abstraction          : 0.01
% 2.77/1.35  MUC search           : 0.00
% 2.77/1.35  Cooper               : 0.00
% 2.77/1.35  Total                : 0.63
% 2.77/1.35  Index Insertion      : 0.00
% 2.77/1.35  Index Deletion       : 0.00
% 2.77/1.35  Index Matching       : 0.00
% 2.77/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
