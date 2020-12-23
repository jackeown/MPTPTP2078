%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1713+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:17 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 170 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 516 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_115,negated_conjecture,(
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
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_49,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_83,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_345,plain,(
    ! [B_64,A_65] :
      ( l1_pre_topc(B_64)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_348,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_345])).

tff(c_357,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_348])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_354,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_345])).

tff(c_361,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_354])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_69,plain,(
    ! [B_34,A_35] :
      ( l1_pre_topc(B_34)
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_69])).

tff(c_81,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72])).

tff(c_28,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_45,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_94,plain,(
    ! [B_38,A_39] :
      ( r1_tsep_1(B_38,A_39)
      | ~ r1_tsep_1(A_39,B_38)
      | ~ l1_struct_0(B_38)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_97,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_94])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_101,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_101])).

tff(c_107,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_14])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_85,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_78])).

tff(c_106,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_108,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_111])).

tff(c_117,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_152,plain,(
    ! [B_51,C_52,A_53] :
      ( r1_tarski(u1_struct_0(B_51),u1_struct_0(C_52))
      | ~ m1_pre_topc(B_51,C_52)
      | ~ m1_pre_topc(C_52,A_53)
      | ~ m1_pre_topc(B_51,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_158,plain,(
    ! [B_51] :
      ( r1_tarski(u1_struct_0(B_51),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_51,'#skF_3')
      | ~ m1_pre_topc(B_51,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_152])).

tff(c_176,plain,(
    ! [B_55] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_55,'#skF_3')
      | ~ m1_pre_topc(B_55,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_158])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_210,plain,(
    ! [B_57] :
      ( k3_xboole_0(u1_struct_0(B_57),u1_struct_0('#skF_3')) = u1_struct_0(B_57)
      | ~ m1_pre_topc(B_57,'#skF_3')
      | ~ m1_pre_topc(B_57,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_176,c_20])).

tff(c_128,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(u1_struct_0(A_42),u1_struct_0(B_43))
      | ~ r1_tsep_1(A_42,B_43)
      | ~ l1_struct_0(B_43)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(u1_struct_0(A_42),u1_struct_0(B_43)) = k1_xboole_0
      | ~ r1_tsep_1(A_42,B_43)
      | ~ l1_struct_0(B_43)
      | ~ l1_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_128,c_6])).

tff(c_216,plain,(
    ! [B_57] :
      ( u1_struct_0(B_57) = k1_xboole_0
      | ~ r1_tsep_1(B_57,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(B_57)
      | ~ m1_pre_topc(B_57,'#skF_3')
      | ~ m1_pre_topc(B_57,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_136])).

tff(c_253,plain,(
    ! [B_60] :
      ( u1_struct_0(B_60) = k1_xboole_0
      | ~ r1_tsep_1(B_60,'#skF_3')
      | ~ l1_struct_0(B_60)
      | ~ m1_pre_topc(B_60,'#skF_3')
      | ~ m1_pre_topc(B_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_216])).

tff(c_256,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_253])).

tff(c_259,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_107,c_256])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_299,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_16])).

tff(c_323,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_52,c_299])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_323])).

tff(c_327,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_326,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_371,plain,(
    ! [B_72,A_73] :
      ( r1_tsep_1(B_72,A_73)
      | ~ r1_tsep_1(A_73,B_72)
      | ~ l1_struct_0(B_72)
      | ~ l1_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_373,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_326,c_371])).

tff(c_376,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_373])).

tff(c_377,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_380,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_377])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_380])).

tff(c_385,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_389,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_385])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_389])).

%------------------------------------------------------------------------------
