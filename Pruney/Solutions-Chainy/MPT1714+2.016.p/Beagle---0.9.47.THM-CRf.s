%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:35 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 238 expanded)
%              Number of leaves         :   32 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 842 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_400,plain,(
    ! [B_111,A_112] :
      ( l1_pre_topc(B_111)
      | ~ m1_pre_topc(B_111,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_403,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_400])).

tff(c_415,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_403])).

tff(c_20,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_406,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_400])).

tff(c_418,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_406])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_328,plain,(
    ! [B_94,A_95] :
      ( l1_pre_topc(B_94)
      | ~ m1_pre_topc(B_94,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_340,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_328])).

tff(c_350,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_340])).

tff(c_331,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_328])).

tff(c_343,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_331])).

tff(c_65,plain,(
    ! [B_41,A_42] :
      ( l1_pre_topc(B_41)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_87,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_77])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_88,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_88])).

tff(c_91,plain,(
    l1_pre_topc('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_68,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_80,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68])).

tff(c_92,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_32,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_105,plain,(
    ! [B_50,A_51] :
      ( r1_tsep_1(B_50,A_51)
      | ~ r1_tsep_1(A_51,B_50)
      | ~ l1_struct_0(B_50)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_105])).

tff(c_109,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_112,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_112])).

tff(c_117,plain,
    ( ~ l1_struct_0('#skF_6')
    | r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_124,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_127,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_127])).

tff(c_133,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_118,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_119,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_43,A_4] :
      ( r1_tarski(A_43,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_100,plain,(
    ! [A_43,A_4] :
      ( r1_tarski(A_43,A_4)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_4)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_97])).

tff(c_123,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(u1_struct_0(B_52),u1_struct_0(A_53))
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_119,c_100])).

tff(c_141,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(u1_struct_0(A_58),u1_struct_0(B_59))
      | ~ r1_tsep_1(A_58,B_59)
      | ~ l1_struct_0(B_59)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_70,B_71,A_72] :
      ( r1_xboole_0(A_70,u1_struct_0(B_71))
      | ~ r1_tarski(A_70,u1_struct_0(A_72))
      | ~ r1_tsep_1(A_72,B_71)
      | ~ l1_struct_0(B_71)
      | ~ l1_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_251,plain,(
    ! [B_86,B_87,A_88] :
      ( r1_xboole_0(u1_struct_0(B_86),u1_struct_0(B_87))
      | ~ r1_tsep_1(A_88,B_87)
      | ~ l1_struct_0(B_87)
      | ~ l1_struct_0(A_88)
      | ~ m1_pre_topc(B_86,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_123,c_172])).

tff(c_255,plain,(
    ! [B_86] :
      ( r1_xboole_0(u1_struct_0(B_86),u1_struct_0('#skF_6'))
      | ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_86,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_251])).

tff(c_272,plain,(
    ! [B_90] :
      ( r1_xboole_0(u1_struct_0(B_90),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_90,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_118,c_133,c_255])).

tff(c_24,plain,(
    ! [A_16,B_18] :
      ( r1_tsep_1(A_16,B_18)
      | ~ r1_xboole_0(u1_struct_0(A_16),u1_struct_0(B_18))
      | ~ l1_struct_0(B_18)
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_275,plain,(
    ! [B_90] :
      ( r1_tsep_1(B_90,'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0(B_90)
      | ~ m1_pre_topc(B_90,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_272,c_24])).

tff(c_302,plain,(
    ! [B_93] :
      ( r1_tsep_1(B_93,'#skF_6')
      | ~ l1_struct_0(B_93)
      | ~ m1_pre_topc(B_93,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_275])).

tff(c_34,plain,
    ( ~ r1_tsep_1('#skF_6','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_57,plain,(
    ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_309,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_302,c_57])).

tff(c_318,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_309])).

tff(c_321,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_318])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_321])).

tff(c_327,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_326,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_369,plain,(
    ! [B_107,A_108] :
      ( r1_tsep_1(B_107,A_108)
      | ~ r1_tsep_1(A_108,B_107)
      | ~ l1_struct_0(B_107)
      | ~ l1_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_371,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_326,c_369])).

tff(c_374,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_371])).

tff(c_380,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_383,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_383])).

tff(c_388,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_392,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_388])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_392])).

tff(c_397,plain,(
    ~ r1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_398,plain,(
    r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_441,plain,(
    ! [B_124,A_125] :
      ( r1_tsep_1(B_124,A_125)
      | ~ r1_tsep_1(A_125,B_124)
      | ~ l1_struct_0(B_124)
      | ~ l1_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_445,plain,
    ( r1_tsep_1('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_398,c_441])).

tff(c_449,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_445])).

tff(c_455,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_458,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_455])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_458])).

tff(c_463,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_467,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_463])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  
% 2.67/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.67/1.33  
% 2.67/1.33  %Foreground sorts:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Background operators:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Foreground operators:
% 2.67/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.67/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.33  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.67/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.33  
% 2.67/1.35  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 2.67/1.35  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.67/1.35  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.67/1.35  tff(f_75, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.67/1.35  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.67/1.35  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.67/1.35  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.67/1.35  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.67/1.35  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.67/1.35  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.67/1.35  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_38, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_400, plain, (![B_111, A_112]: (l1_pre_topc(B_111) | ~m1_pre_topc(B_111, A_112) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.35  tff(c_403, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_400])).
% 2.67/1.35  tff(c_415, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_403])).
% 2.67/1.35  tff(c_20, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.35  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_406, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_400])).
% 2.67/1.35  tff(c_418, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_406])).
% 2.67/1.35  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_328, plain, (![B_94, A_95]: (l1_pre_topc(B_94) | ~m1_pre_topc(B_94, A_95) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.35  tff(c_340, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_328])).
% 2.67/1.35  tff(c_350, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_340])).
% 2.67/1.35  tff(c_331, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_328])).
% 2.67/1.35  tff(c_343, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_331])).
% 2.67/1.35  tff(c_65, plain, (![B_41, A_42]: (l1_pre_topc(B_41) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.35  tff(c_77, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_65])).
% 2.67/1.35  tff(c_87, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_77])).
% 2.67/1.35  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_84, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_65])).
% 2.67/1.35  tff(c_88, plain, (~l1_pre_topc('#skF_5')), inference(splitLeft, [status(thm)], [c_84])).
% 2.67/1.35  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_88])).
% 2.67/1.35  tff(c_91, plain, (l1_pre_topc('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 2.67/1.35  tff(c_68, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_65])).
% 2.67/1.35  tff(c_80, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68])).
% 2.67/1.35  tff(c_92, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_84])).
% 2.67/1.35  tff(c_32, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_58, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 2.67/1.35  tff(c_105, plain, (![B_50, A_51]: (r1_tsep_1(B_50, A_51) | ~r1_tsep_1(A_51, B_50) | ~l1_struct_0(B_50) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.35  tff(c_108, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_105])).
% 2.67/1.35  tff(c_109, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_108])).
% 2.67/1.35  tff(c_112, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.67/1.35  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_112])).
% 2.67/1.35  tff(c_117, plain, (~l1_struct_0('#skF_6') | r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_108])).
% 2.67/1.35  tff(c_124, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_117])).
% 2.67/1.35  tff(c_127, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_124])).
% 2.67/1.35  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_127])).
% 2.67/1.35  tff(c_133, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_117])).
% 2.67/1.35  tff(c_118, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_108])).
% 2.67/1.35  tff(c_119, plain, (![B_52, A_53]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.35  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.35  tff(c_93, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.35  tff(c_4, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.35  tff(c_97, plain, (![A_43, A_4]: (r1_tarski(A_43, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_43, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_93, c_4])).
% 2.67/1.35  tff(c_100, plain, (![A_43, A_4]: (r1_tarski(A_43, A_4) | ~m1_subset_1(A_43, k1_zfmisc_1(A_4)))), inference(negUnitSimplification, [status(thm)], [c_16, c_97])).
% 2.67/1.35  tff(c_123, plain, (![B_52, A_53]: (r1_tarski(u1_struct_0(B_52), u1_struct_0(A_53)) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_119, c_100])).
% 2.67/1.35  tff(c_141, plain, (![A_58, B_59]: (r1_xboole_0(u1_struct_0(A_58), u1_struct_0(B_59)) | ~r1_tsep_1(A_58, B_59) | ~l1_struct_0(B_59) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.35  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.35  tff(c_172, plain, (![A_70, B_71, A_72]: (r1_xboole_0(A_70, u1_struct_0(B_71)) | ~r1_tarski(A_70, u1_struct_0(A_72)) | ~r1_tsep_1(A_72, B_71) | ~l1_struct_0(B_71) | ~l1_struct_0(A_72))), inference(resolution, [status(thm)], [c_141, c_2])).
% 2.67/1.35  tff(c_251, plain, (![B_86, B_87, A_88]: (r1_xboole_0(u1_struct_0(B_86), u1_struct_0(B_87)) | ~r1_tsep_1(A_88, B_87) | ~l1_struct_0(B_87) | ~l1_struct_0(A_88) | ~m1_pre_topc(B_86, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_123, c_172])).
% 2.67/1.35  tff(c_255, plain, (![B_86]: (r1_xboole_0(u1_struct_0(B_86), u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | ~m1_pre_topc(B_86, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_251])).
% 2.67/1.35  tff(c_272, plain, (![B_90]: (r1_xboole_0(u1_struct_0(B_90), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_90, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_118, c_133, c_255])).
% 2.67/1.35  tff(c_24, plain, (![A_16, B_18]: (r1_tsep_1(A_16, B_18) | ~r1_xboole_0(u1_struct_0(A_16), u1_struct_0(B_18)) | ~l1_struct_0(B_18) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.67/1.35  tff(c_275, plain, (![B_90]: (r1_tsep_1(B_90, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(B_90) | ~m1_pre_topc(B_90, '#skF_5'))), inference(resolution, [status(thm)], [c_272, c_24])).
% 2.67/1.35  tff(c_302, plain, (![B_93]: (r1_tsep_1(B_93, '#skF_6') | ~l1_struct_0(B_93) | ~m1_pre_topc(B_93, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_275])).
% 2.67/1.35  tff(c_34, plain, (~r1_tsep_1('#skF_6', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.67/1.35  tff(c_57, plain, (~r1_tsep_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 2.67/1.35  tff(c_309, plain, (~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_302, c_57])).
% 2.67/1.35  tff(c_318, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_309])).
% 2.67/1.35  tff(c_321, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_318])).
% 2.67/1.35  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_321])).
% 2.67/1.35  tff(c_327, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 2.67/1.35  tff(c_326, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 2.67/1.35  tff(c_369, plain, (![B_107, A_108]: (r1_tsep_1(B_107, A_108) | ~r1_tsep_1(A_108, B_107) | ~l1_struct_0(B_107) | ~l1_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.35  tff(c_371, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_326, c_369])).
% 2.67/1.35  tff(c_374, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_327, c_371])).
% 2.67/1.35  tff(c_380, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_374])).
% 2.67/1.35  tff(c_383, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_380])).
% 2.67/1.35  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_383])).
% 2.67/1.35  tff(c_388, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_374])).
% 2.67/1.35  tff(c_392, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_388])).
% 2.67/1.35  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_350, c_392])).
% 2.67/1.35  tff(c_397, plain, (~r1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.67/1.35  tff(c_398, plain, (r1_tsep_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 2.67/1.35  tff(c_441, plain, (![B_124, A_125]: (r1_tsep_1(B_124, A_125) | ~r1_tsep_1(A_125, B_124) | ~l1_struct_0(B_124) | ~l1_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.35  tff(c_445, plain, (r1_tsep_1('#skF_6', '#skF_4') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_398, c_441])).
% 2.67/1.35  tff(c_449, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_397, c_445])).
% 2.67/1.35  tff(c_455, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_449])).
% 2.67/1.35  tff(c_458, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_455])).
% 2.67/1.35  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_418, c_458])).
% 2.67/1.35  tff(c_463, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_449])).
% 2.67/1.35  tff(c_467, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_463])).
% 2.67/1.35  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_415, c_467])).
% 2.67/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.35  
% 2.67/1.35  Inference rules
% 2.67/1.35  ----------------------
% 2.67/1.35  #Ref     : 0
% 2.67/1.35  #Sup     : 68
% 2.67/1.35  #Fact    : 0
% 2.67/1.35  #Define  : 0
% 2.67/1.35  #Split   : 8
% 2.67/1.35  #Chain   : 0
% 2.67/1.35  #Close   : 0
% 2.67/1.35  
% 2.67/1.35  Ordering : KBO
% 2.67/1.35  
% 2.67/1.35  Simplification rules
% 2.67/1.35  ----------------------
% 2.67/1.35  #Subsume      : 1
% 2.67/1.35  #Demod        : 37
% 2.67/1.35  #Tautology    : 14
% 2.67/1.35  #SimpNegUnit  : 8
% 2.67/1.35  #BackRed      : 0
% 2.67/1.35  
% 2.67/1.35  #Partial instantiations: 0
% 2.67/1.35  #Strategies tried      : 1
% 2.67/1.35  
% 2.67/1.35  Timing (in seconds)
% 2.67/1.35  ----------------------
% 2.67/1.35  Preprocessing        : 0.29
% 2.67/1.35  Parsing              : 0.16
% 2.67/1.35  CNF conversion       : 0.02
% 2.67/1.35  Main loop            : 0.28
% 2.67/1.35  Inferencing          : 0.11
% 2.67/1.35  Reduction            : 0.07
% 2.67/1.35  Demodulation         : 0.05
% 2.67/1.35  BG Simplification    : 0.02
% 2.67/1.35  Subsumption          : 0.05
% 2.67/1.35  Abstraction          : 0.01
% 2.67/1.35  MUC search           : 0.00
% 2.67/1.35  Cooper               : 0.00
% 2.67/1.35  Total                : 0.61
% 2.67/1.35  Index Insertion      : 0.00
% 2.67/1.35  Index Deletion       : 0.00
% 2.67/1.35  Index Matching       : 0.00
% 2.67/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
