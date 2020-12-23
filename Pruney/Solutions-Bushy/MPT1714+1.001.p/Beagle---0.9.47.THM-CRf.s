%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1714+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:17 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 227 expanded)
%              Number of leaves         :   34 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 809 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_626,plain,(
    ! [B_157,A_158] :
      ( l1_pre_topc(B_157)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_641,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_626])).

tff(c_652,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_641])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    m1_pre_topc('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_632,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_626])).

tff(c_645,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_632])).

tff(c_524,plain,(
    ! [B_129,A_130] :
      ( l1_pre_topc(B_129)
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_530,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_524])).

tff(c_543,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_530])).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_536,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_524])).

tff(c_547,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_536])).

tff(c_94,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_94])).

tff(c_117,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_106])).

tff(c_42,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_113,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_100])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_120,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_109])).

tff(c_38,plain,
    ( r1_tsep_1('#skF_8','#skF_7')
    | r1_tsep_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_79,plain,(
    r1_tsep_1('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_149,plain,(
    ! [B_68,A_69] :
      ( r1_tsep_1(B_68,A_69)
      | ~ r1_tsep_1(A_69,B_68)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_152,plain,
    ( r1_tsep_1('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_79,c_149])).

tff(c_153,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_164,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_164])).

tff(c_169,plain,
    ( ~ l1_struct_0('#skF_8')
    | r1_tsep_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_171,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_174,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_174])).

tff(c_180,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_170,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_190,plain,(
    ! [B_75,A_76] :
      ( m1_subset_1(u1_struct_0(B_75),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_197,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0(A_76))
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_190,c_28])).

tff(c_202,plain,(
    ! [A_79,B_80] :
      ( r1_xboole_0(u1_struct_0(A_79),u1_struct_0(B_80))
      | ~ r1_tsep_1(A_79,B_80)
      | ~ l1_struct_0(B_80)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_26,C_28,B_27] :
      ( r1_xboole_0(A_26,C_28)
      | ~ r1_xboole_0(B_27,C_28)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_285,plain,(
    ! [A_95,B_96,A_97] :
      ( r1_xboole_0(A_95,u1_struct_0(B_96))
      | ~ r1_tarski(A_95,u1_struct_0(A_97))
      | ~ r1_tsep_1(A_97,B_96)
      | ~ l1_struct_0(B_96)
      | ~ l1_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_202,c_34])).

tff(c_395,plain,(
    ! [B_117,B_118,A_119] :
      ( r1_xboole_0(u1_struct_0(B_117),u1_struct_0(B_118))
      | ~ r1_tsep_1(A_119,B_118)
      | ~ l1_struct_0(B_118)
      | ~ l1_struct_0(A_119)
      | ~ m1_pre_topc(B_117,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_197,c_285])).

tff(c_399,plain,(
    ! [B_117] :
      ( r1_xboole_0(u1_struct_0(B_117),u1_struct_0('#skF_8'))
      | ~ l1_struct_0('#skF_8')
      | ~ l1_struct_0('#skF_7')
      | ~ m1_pre_topc(B_117,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_79,c_395])).

tff(c_419,plain,(
    ! [B_121] :
      ( r1_xboole_0(u1_struct_0(B_121),u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(B_121,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_170,c_180,c_399])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( r1_tsep_1(A_1,B_3)
      | ~ r1_xboole_0(u1_struct_0(A_1),u1_struct_0(B_3))
      | ~ l1_struct_0(B_3)
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_422,plain,(
    ! [B_121] :
      ( r1_tsep_1(B_121,'#skF_8')
      | ~ l1_struct_0('#skF_8')
      | ~ l1_struct_0(B_121)
      | ~ m1_pre_topc(B_121,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_419,c_2])).

tff(c_476,plain,(
    ! [B_124] :
      ( r1_tsep_1(B_124,'#skF_8')
      | ~ l1_struct_0(B_124)
      | ~ m1_pre_topc(B_124,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_422])).

tff(c_40,plain,
    ( ~ r1_tsep_1('#skF_8','#skF_6')
    | ~ r1_tsep_1('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_80,plain,(
    ~ r1_tsep_1('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_491,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_476,c_80])).

tff(c_512,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_491])).

tff(c_515,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_512])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_515])).

tff(c_520,plain,(
    ~ r1_tsep_1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_521,plain,(
    r1_tsep_1('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_584,plain,(
    ! [B_148,A_149] :
      ( r1_tsep_1(B_148,A_149)
      | ~ r1_tsep_1(A_149,B_148)
      | ~ l1_struct_0(B_148)
      | ~ l1_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_586,plain,
    ( r1_tsep_1('#skF_8','#skF_6')
    | ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_521,c_584])).

tff(c_591,plain,
    ( ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_586])).

tff(c_593,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_596,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_593])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_596])).

tff(c_601,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_605,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_601])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_605])).

tff(c_611,plain,(
    ~ r1_tsep_1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_610,plain,(
    r1_tsep_1('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_676,plain,(
    ! [B_173,A_174] :
      ( r1_tsep_1(B_173,A_174)
      | ~ r1_tsep_1(A_174,B_173)
      | ~ l1_struct_0(B_173)
      | ~ l1_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_678,plain,
    ( r1_tsep_1('#skF_7','#skF_8')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_610,c_676])).

tff(c_681,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_678])).

tff(c_682,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_681])).

tff(c_693,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_682])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_693])).

tff(c_698,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_702,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_698])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_702])).

%------------------------------------------------------------------------------
