%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:34 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 211 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  205 ( 825 expanded)
%              Number of equality atoms :    1 (   1 expanded)
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

tff(f_119,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_546,plain,(
    ! [B_93,A_94] :
      ( l1_pre_topc(B_93)
      | ~ m1_pre_topc(B_93,A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_555,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_546])).

tff(c_565,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_555])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_549,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_546])).

tff(c_561,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_549])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_488,plain,(
    ! [B_87,A_88] :
      ( l1_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_500,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_488])).

tff(c_510,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_500])).

tff(c_497,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_488])).

tff(c_507,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_497])).

tff(c_52,plain,(
    ! [B_36,A_37] :
      ( l1_pre_topc(B_36)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_67,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_55])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_71,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_61])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_24,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_51,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_83,plain,(
    ! [B_40,A_41] :
      ( r1_tsep_1(B_40,A_41)
      | ~ r1_tsep_1(A_41,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_83])).

tff(c_87,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_90,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_90])).

tff(c_95,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_101,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_101])).

tff(c_107,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_96,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_122,plain,(
    ! [B_50,C_51,A_52] :
      ( r1_tarski(u1_struct_0(B_50),u1_struct_0(C_51))
      | ~ m1_pre_topc(B_50,C_51)
      | ~ m1_pre_topc(C_51,A_52)
      | ~ m1_pre_topc(B_50,A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_130,plain,(
    ! [B_50] :
      ( r1_tarski(u1_struct_0(B_50),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_50,'#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_142,plain,(
    ! [B_50] :
      ( r1_tarski(u1_struct_0(B_50),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_50,'#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_130])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( r1_xboole_0(u1_struct_0(A_11),u1_struct_0(B_13))
      | ~ r1_tsep_1(A_11,B_13)
      | ~ l1_struct_0(B_13)
      | ~ l1_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r1_xboole_0(A_44,C_45)
      | ~ r1_xboole_0(B_46,D_47)
      | ~ r1_tarski(C_45,D_47)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_275,plain,(
    ! [A_62,C_63,B_64,A_65] :
      ( r1_xboole_0(A_62,C_63)
      | ~ r1_tarski(C_63,u1_struct_0(B_64))
      | ~ r1_tarski(A_62,u1_struct_0(A_65))
      | ~ r1_tsep_1(A_65,B_64)
      | ~ l1_struct_0(B_64)
      | ~ l1_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_356,plain,(
    ! [A_68,B_69,A_70] :
      ( r1_xboole_0(A_68,u1_struct_0(B_69))
      | ~ r1_tarski(A_68,u1_struct_0(A_70))
      | ~ r1_tsep_1(A_70,B_69)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_360,plain,(
    ! [B_50,B_69] :
      ( r1_xboole_0(u1_struct_0(B_50),u1_struct_0(B_69))
      | ~ r1_tsep_1('#skF_3',B_69)
      | ~ l1_struct_0(B_69)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_3')
      | ~ m1_pre_topc(B_50,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_142,c_356])).

tff(c_382,plain,(
    ! [B_73,B_74] :
      ( r1_xboole_0(u1_struct_0(B_73),u1_struct_0(B_74))
      | ~ r1_tsep_1('#skF_3',B_74)
      | ~ l1_struct_0(B_74)
      | ~ m1_pre_topc(B_73,'#skF_3')
      | ~ m1_pre_topc(B_73,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_360])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( r1_tsep_1(A_11,B_13)
      | ~ r1_xboole_0(u1_struct_0(A_11),u1_struct_0(B_13))
      | ~ l1_struct_0(B_13)
      | ~ l1_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_440,plain,(
    ! [B_84,B_85] :
      ( r1_tsep_1(B_84,B_85)
      | ~ l1_struct_0(B_84)
      | ~ r1_tsep_1('#skF_3',B_85)
      | ~ l1_struct_0(B_85)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_382,c_14])).

tff(c_447,plain,(
    ! [B_84] :
      ( r1_tsep_1(B_84,'#skF_4')
      | ~ l1_struct_0(B_84)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_51,c_440])).

tff(c_455,plain,(
    ! [B_86] :
      ( r1_tsep_1(B_86,'#skF_4')
      | ~ l1_struct_0(B_86)
      | ~ m1_pre_topc(B_86,'#skF_3')
      | ~ m1_pre_topc(B_86,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_447])).

tff(c_26,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_466,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_455,c_50])).

tff(c_478,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_466])).

tff(c_481,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_478])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_481])).

tff(c_487,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_486,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_520,plain,(
    ! [B_91,A_92] :
      ( r1_tsep_1(B_91,A_92)
      | ~ r1_tsep_1(A_92,B_91)
      | ~ l1_struct_0(B_91)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_522,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_486,c_520])).

tff(c_525,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_522])).

tff(c_526,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_529,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_526])).

tff(c_533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_529])).

tff(c_534,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_538,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_534])).

tff(c_542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_538])).

tff(c_543,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_544,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_583,plain,(
    ! [B_97,A_98] :
      ( r1_tsep_1(B_97,A_98)
      | ~ r1_tsep_1(A_98,B_97)
      | ~ l1_struct_0(B_97)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_587,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_544,c_583])).

tff(c_591,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_587])).

tff(c_592,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_595,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_592])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_595])).

tff(c_600,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_604,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_600])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.42  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.42  
% 2.63/1.42  %Foreground sorts:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Background operators:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Foreground operators:
% 2.63/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.63/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.42  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.63/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.42  
% 2.63/1.44  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.63/1.44  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.63/1.44  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.63/1.44  tff(f_67, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.63/1.44  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.63/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.63/1.44  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.63/1.44  tff(f_39, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.63/1.44  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_546, plain, (![B_93, A_94]: (l1_pre_topc(B_93) | ~m1_pre_topc(B_93, A_94) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.44  tff(c_555, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_546])).
% 2.63/1.44  tff(c_565, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_555])).
% 2.63/1.44  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.44  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_549, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_546])).
% 2.63/1.44  tff(c_561, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_549])).
% 2.63/1.44  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_488, plain, (![B_87, A_88]: (l1_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.44  tff(c_500, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_488])).
% 2.63/1.44  tff(c_510, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_500])).
% 2.63/1.44  tff(c_497, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_488])).
% 2.63/1.44  tff(c_507, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_497])).
% 2.63/1.44  tff(c_52, plain, (![B_36, A_37]: (l1_pre_topc(B_36) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.44  tff(c_55, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_52])).
% 2.63/1.44  tff(c_67, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_55])).
% 2.63/1.44  tff(c_28, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_61, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_52])).
% 2.63/1.44  tff(c_71, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_61])).
% 2.63/1.44  tff(c_64, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.63/1.44  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 2.63/1.44  tff(c_24, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_51, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.63/1.44  tff(c_83, plain, (![B_40, A_41]: (r1_tsep_1(B_40, A_41) | ~r1_tsep_1(A_41, B_40) | ~l1_struct_0(B_40) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.44  tff(c_86, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_51, c_83])).
% 2.63/1.44  tff(c_87, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_86])).
% 2.63/1.44  tff(c_90, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_87])).
% 2.63/1.44  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_90])).
% 2.63/1.44  tff(c_95, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 2.63/1.44  tff(c_98, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_95])).
% 2.63/1.44  tff(c_101, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_98])).
% 2.63/1.44  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_101])).
% 2.63/1.44  tff(c_107, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_95])).
% 2.63/1.44  tff(c_96, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 2.63/1.44  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_122, plain, (![B_50, C_51, A_52]: (r1_tarski(u1_struct_0(B_50), u1_struct_0(C_51)) | ~m1_pre_topc(B_50, C_51) | ~m1_pre_topc(C_51, A_52) | ~m1_pre_topc(B_50, A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.63/1.44  tff(c_130, plain, (![B_50]: (r1_tarski(u1_struct_0(B_50), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_50, '#skF_3') | ~m1_pre_topc(B_50, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_122])).
% 2.63/1.44  tff(c_142, plain, (![B_50]: (r1_tarski(u1_struct_0(B_50), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_50, '#skF_3') | ~m1_pre_topc(B_50, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_130])).
% 2.63/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.44  tff(c_16, plain, (![A_11, B_13]: (r1_xboole_0(u1_struct_0(A_11), u1_struct_0(B_13)) | ~r1_tsep_1(A_11, B_13) | ~l1_struct_0(B_13) | ~l1_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.44  tff(c_113, plain, (![A_44, C_45, B_46, D_47]: (r1_xboole_0(A_44, C_45) | ~r1_xboole_0(B_46, D_47) | ~r1_tarski(C_45, D_47) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.44  tff(c_275, plain, (![A_62, C_63, B_64, A_65]: (r1_xboole_0(A_62, C_63) | ~r1_tarski(C_63, u1_struct_0(B_64)) | ~r1_tarski(A_62, u1_struct_0(A_65)) | ~r1_tsep_1(A_65, B_64) | ~l1_struct_0(B_64) | ~l1_struct_0(A_65))), inference(resolution, [status(thm)], [c_16, c_113])).
% 2.63/1.44  tff(c_356, plain, (![A_68, B_69, A_70]: (r1_xboole_0(A_68, u1_struct_0(B_69)) | ~r1_tarski(A_68, u1_struct_0(A_70)) | ~r1_tsep_1(A_70, B_69) | ~l1_struct_0(B_69) | ~l1_struct_0(A_70))), inference(resolution, [status(thm)], [c_6, c_275])).
% 2.63/1.44  tff(c_360, plain, (![B_50, B_69]: (r1_xboole_0(u1_struct_0(B_50), u1_struct_0(B_69)) | ~r1_tsep_1('#skF_3', B_69) | ~l1_struct_0(B_69) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_50, '#skF_3') | ~m1_pre_topc(B_50, '#skF_1'))), inference(resolution, [status(thm)], [c_142, c_356])).
% 2.63/1.44  tff(c_382, plain, (![B_73, B_74]: (r1_xboole_0(u1_struct_0(B_73), u1_struct_0(B_74)) | ~r1_tsep_1('#skF_3', B_74) | ~l1_struct_0(B_74) | ~m1_pre_topc(B_73, '#skF_3') | ~m1_pre_topc(B_73, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_360])).
% 2.63/1.44  tff(c_14, plain, (![A_11, B_13]: (r1_tsep_1(A_11, B_13) | ~r1_xboole_0(u1_struct_0(A_11), u1_struct_0(B_13)) | ~l1_struct_0(B_13) | ~l1_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.44  tff(c_440, plain, (![B_84, B_85]: (r1_tsep_1(B_84, B_85) | ~l1_struct_0(B_84) | ~r1_tsep_1('#skF_3', B_85) | ~l1_struct_0(B_85) | ~m1_pre_topc(B_84, '#skF_3') | ~m1_pre_topc(B_84, '#skF_1'))), inference(resolution, [status(thm)], [c_382, c_14])).
% 2.63/1.44  tff(c_447, plain, (![B_84]: (r1_tsep_1(B_84, '#skF_4') | ~l1_struct_0(B_84) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_84, '#skF_3') | ~m1_pre_topc(B_84, '#skF_1'))), inference(resolution, [status(thm)], [c_51, c_440])).
% 2.63/1.44  tff(c_455, plain, (![B_86]: (r1_tsep_1(B_86, '#skF_4') | ~l1_struct_0(B_86) | ~m1_pre_topc(B_86, '#skF_3') | ~m1_pre_topc(B_86, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_447])).
% 2.63/1.44  tff(c_26, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.44  tff(c_50, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.63/1.44  tff(c_466, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_455, c_50])).
% 2.63/1.44  tff(c_478, plain, (~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28, c_466])).
% 2.63/1.44  tff(c_481, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_478])).
% 2.63/1.44  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_481])).
% 2.63/1.44  tff(c_487, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 2.63/1.44  tff(c_486, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 2.63/1.44  tff(c_520, plain, (![B_91, A_92]: (r1_tsep_1(B_91, A_92) | ~r1_tsep_1(A_92, B_91) | ~l1_struct_0(B_91) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.44  tff(c_522, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_486, c_520])).
% 2.63/1.44  tff(c_525, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_487, c_522])).
% 2.63/1.44  tff(c_526, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_525])).
% 2.63/1.44  tff(c_529, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_526])).
% 2.63/1.44  tff(c_533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_507, c_529])).
% 2.63/1.44  tff(c_534, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_525])).
% 2.63/1.44  tff(c_538, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_534])).
% 2.63/1.44  tff(c_542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_510, c_538])).
% 2.63/1.44  tff(c_543, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.63/1.44  tff(c_544, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.63/1.44  tff(c_583, plain, (![B_97, A_98]: (r1_tsep_1(B_97, A_98) | ~r1_tsep_1(A_98, B_97) | ~l1_struct_0(B_97) | ~l1_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.44  tff(c_587, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_544, c_583])).
% 2.63/1.44  tff(c_591, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_543, c_587])).
% 2.63/1.44  tff(c_592, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_591])).
% 2.63/1.44  tff(c_595, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_592])).
% 2.63/1.44  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_561, c_595])).
% 2.63/1.44  tff(c_600, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_591])).
% 2.63/1.44  tff(c_604, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_600])).
% 2.63/1.44  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_565, c_604])).
% 2.63/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.44  
% 2.63/1.44  Inference rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Ref     : 0
% 2.63/1.44  #Sup     : 94
% 2.63/1.44  #Fact    : 0
% 2.63/1.44  #Define  : 0
% 2.63/1.44  #Split   : 14
% 2.63/1.44  #Chain   : 0
% 2.63/1.44  #Close   : 0
% 2.63/1.44  
% 2.63/1.44  Ordering : KBO
% 2.63/1.44  
% 2.63/1.44  Simplification rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Subsume      : 9
% 2.63/1.44  #Demod        : 111
% 2.63/1.44  #Tautology    : 26
% 2.63/1.44  #SimpNegUnit  : 2
% 2.63/1.44  #BackRed      : 0
% 2.63/1.44  
% 2.63/1.44  #Partial instantiations: 0
% 2.63/1.44  #Strategies tried      : 1
% 2.63/1.44  
% 2.63/1.44  Timing (in seconds)
% 2.63/1.44  ----------------------
% 2.63/1.44  Preprocessing        : 0.29
% 2.63/1.44  Parsing              : 0.16
% 2.63/1.44  CNF conversion       : 0.02
% 2.63/1.44  Main loop            : 0.31
% 2.63/1.44  Inferencing          : 0.12
% 2.63/1.44  Reduction            : 0.09
% 2.63/1.44  Demodulation         : 0.06
% 2.63/1.44  BG Simplification    : 0.02
% 2.63/1.44  Subsumption          : 0.06
% 2.63/1.44  Abstraction          : 0.01
% 2.63/1.44  MUC search           : 0.00
% 2.63/1.44  Cooper               : 0.00
% 2.63/1.44  Total                : 0.64
% 2.63/1.44  Index Insertion      : 0.00
% 2.63/1.44  Index Deletion       : 0.00
% 2.63/1.44  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
