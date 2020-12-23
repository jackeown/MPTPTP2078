%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:38 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.73s
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
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

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

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_404,plain,(
    ! [B_111,A_112] :
      ( l1_pre_topc(B_111)
      | ~ m1_pre_topc(B_111,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_416,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_404])).

tff(c_426,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_416])).

tff(c_20,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_407,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_404])).

tff(c_419,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_407])).

tff(c_328,plain,(
    ! [B_94,A_95] :
      ( l1_pre_topc(B_94)
      | ~ m1_pre_topc(B_94,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_331,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_328])).

tff(c_343,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_331])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_334,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_328])).

tff(c_346,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_334])).

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

tff(c_34,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_57,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

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
    inference(resolution,[status(thm)],[c_57,c_105])).

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
    inference(resolution,[status(thm)],[c_57,c_251])).

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

tff(c_32,plain,
    ( ~ r1_tsep_1('#skF_6','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    ~ r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_309,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_302,c_58])).

tff(c_318,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_309])).

tff(c_321,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_318])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_321])).

tff(c_326,plain,(
    ~ r1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_327,plain,(
    r1_tsep_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_369,plain,(
    ! [B_107,A_108] :
      ( r1_tsep_1(B_107,A_108)
      | ~ r1_tsep_1(A_108,B_107)
      | ~ l1_struct_0(B_107)
      | ~ l1_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_371,plain,
    ( r1_tsep_1('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_369])).

tff(c_376,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_371])).

tff(c_383,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_386,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_386])).

tff(c_391,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_396,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_391])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_396])).

tff(c_402,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_401,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_445,plain,(
    ! [B_124,A_125] :
      ( r1_tsep_1(B_124,A_125)
      | ~ r1_tsep_1(A_125,B_124)
      | ~ l1_struct_0(B_124)
      | ~ l1_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_447,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_401,c_445])).

tff(c_450,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_402,c_447])).

tff(c_451,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_454,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_451])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_454])).

tff(c_459,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_463,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_459])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  
% 2.43/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.43/1.33  
% 2.43/1.33  %Foreground sorts:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Background operators:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Foreground operators:
% 2.43/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.43/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.43/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.43/1.33  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.43/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.33  
% 2.73/1.35  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 2.73/1.35  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.73/1.35  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.73/1.35  tff(f_75, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.73/1.35  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.73/1.35  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.73/1.35  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.35  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.73/1.35  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.73/1.35  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.73/1.35  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_404, plain, (![B_111, A_112]: (l1_pre_topc(B_111) | ~m1_pre_topc(B_111, A_112) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.35  tff(c_416, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_404])).
% 2.73/1.35  tff(c_426, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_416])).
% 2.73/1.35  tff(c_20, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.73/1.35  tff(c_38, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_407, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_404])).
% 2.73/1.35  tff(c_419, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_407])).
% 2.73/1.35  tff(c_328, plain, (![B_94, A_95]: (l1_pre_topc(B_94) | ~m1_pre_topc(B_94, A_95) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.35  tff(c_331, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_328])).
% 2.73/1.35  tff(c_343, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_331])).
% 2.73/1.35  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_334, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_328])).
% 2.73/1.35  tff(c_346, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_334])).
% 2.73/1.35  tff(c_65, plain, (![B_41, A_42]: (l1_pre_topc(B_41) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.35  tff(c_77, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_65])).
% 2.73/1.35  tff(c_87, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_77])).
% 2.73/1.35  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_84, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_65])).
% 2.73/1.35  tff(c_88, plain, (~l1_pre_topc('#skF_5')), inference(splitLeft, [status(thm)], [c_84])).
% 2.73/1.35  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_88])).
% 2.73/1.35  tff(c_91, plain, (l1_pre_topc('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 2.73/1.35  tff(c_68, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_65])).
% 2.73/1.35  tff(c_80, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68])).
% 2.73/1.35  tff(c_92, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_84])).
% 2.73/1.35  tff(c_34, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_57, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 2.73/1.35  tff(c_105, plain, (![B_50, A_51]: (r1_tsep_1(B_50, A_51) | ~r1_tsep_1(A_51, B_50) | ~l1_struct_0(B_50) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.35  tff(c_108, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_57, c_105])).
% 2.73/1.35  tff(c_109, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_108])).
% 2.73/1.35  tff(c_112, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.73/1.35  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_112])).
% 2.73/1.35  tff(c_117, plain, (~l1_struct_0('#skF_6') | r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_108])).
% 2.73/1.35  tff(c_124, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_117])).
% 2.73/1.35  tff(c_127, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_124])).
% 2.73/1.35  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_127])).
% 2.73/1.35  tff(c_133, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_117])).
% 2.73/1.35  tff(c_118, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_108])).
% 2.73/1.35  tff(c_119, plain, (![B_52, A_53]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.35  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.35  tff(c_93, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.35  tff(c_4, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.35  tff(c_97, plain, (![A_43, A_4]: (r1_tarski(A_43, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_43, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_93, c_4])).
% 2.73/1.35  tff(c_100, plain, (![A_43, A_4]: (r1_tarski(A_43, A_4) | ~m1_subset_1(A_43, k1_zfmisc_1(A_4)))), inference(negUnitSimplification, [status(thm)], [c_16, c_97])).
% 2.73/1.35  tff(c_123, plain, (![B_52, A_53]: (r1_tarski(u1_struct_0(B_52), u1_struct_0(A_53)) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_119, c_100])).
% 2.73/1.35  tff(c_141, plain, (![A_58, B_59]: (r1_xboole_0(u1_struct_0(A_58), u1_struct_0(B_59)) | ~r1_tsep_1(A_58, B_59) | ~l1_struct_0(B_59) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.35  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.35  tff(c_172, plain, (![A_70, B_71, A_72]: (r1_xboole_0(A_70, u1_struct_0(B_71)) | ~r1_tarski(A_70, u1_struct_0(A_72)) | ~r1_tsep_1(A_72, B_71) | ~l1_struct_0(B_71) | ~l1_struct_0(A_72))), inference(resolution, [status(thm)], [c_141, c_2])).
% 2.73/1.35  tff(c_251, plain, (![B_86, B_87, A_88]: (r1_xboole_0(u1_struct_0(B_86), u1_struct_0(B_87)) | ~r1_tsep_1(A_88, B_87) | ~l1_struct_0(B_87) | ~l1_struct_0(A_88) | ~m1_pre_topc(B_86, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_123, c_172])).
% 2.73/1.35  tff(c_255, plain, (![B_86]: (r1_xboole_0(u1_struct_0(B_86), u1_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | ~m1_pre_topc(B_86, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_57, c_251])).
% 2.73/1.35  tff(c_272, plain, (![B_90]: (r1_xboole_0(u1_struct_0(B_90), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_90, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_118, c_133, c_255])).
% 2.73/1.35  tff(c_24, plain, (![A_16, B_18]: (r1_tsep_1(A_16, B_18) | ~r1_xboole_0(u1_struct_0(A_16), u1_struct_0(B_18)) | ~l1_struct_0(B_18) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.35  tff(c_275, plain, (![B_90]: (r1_tsep_1(B_90, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(B_90) | ~m1_pre_topc(B_90, '#skF_5'))), inference(resolution, [status(thm)], [c_272, c_24])).
% 2.73/1.35  tff(c_302, plain, (![B_93]: (r1_tsep_1(B_93, '#skF_6') | ~l1_struct_0(B_93) | ~m1_pre_topc(B_93, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_275])).
% 2.73/1.35  tff(c_32, plain, (~r1_tsep_1('#skF_6', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.73/1.35  tff(c_58, plain, (~r1_tsep_1('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 2.73/1.35  tff(c_309, plain, (~l1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_302, c_58])).
% 2.73/1.35  tff(c_318, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_309])).
% 2.73/1.35  tff(c_321, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_318])).
% 2.73/1.35  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_321])).
% 2.73/1.35  tff(c_326, plain, (~r1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.73/1.35  tff(c_327, plain, (r1_tsep_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 2.73/1.35  tff(c_369, plain, (![B_107, A_108]: (r1_tsep_1(B_107, A_108) | ~r1_tsep_1(A_108, B_107) | ~l1_struct_0(B_107) | ~l1_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.35  tff(c_371, plain, (r1_tsep_1('#skF_6', '#skF_4') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_327, c_369])).
% 2.73/1.35  tff(c_376, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_326, c_371])).
% 2.73/1.35  tff(c_383, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_376])).
% 2.73/1.35  tff(c_386, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_383])).
% 2.73/1.35  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_346, c_386])).
% 2.73/1.35  tff(c_391, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_376])).
% 2.73/1.35  tff(c_396, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_391])).
% 2.73/1.35  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_396])).
% 2.73/1.35  tff(c_402, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 2.73/1.35  tff(c_401, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 2.73/1.35  tff(c_445, plain, (![B_124, A_125]: (r1_tsep_1(B_124, A_125) | ~r1_tsep_1(A_125, B_124) | ~l1_struct_0(B_124) | ~l1_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.35  tff(c_447, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_401, c_445])).
% 2.73/1.35  tff(c_450, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_402, c_447])).
% 2.73/1.35  tff(c_451, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_450])).
% 2.73/1.35  tff(c_454, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_451])).
% 2.73/1.35  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_419, c_454])).
% 2.73/1.35  tff(c_459, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_450])).
% 2.73/1.35  tff(c_463, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_459])).
% 2.73/1.35  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_426, c_463])).
% 2.73/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.35  
% 2.73/1.35  Inference rules
% 2.73/1.35  ----------------------
% 2.73/1.35  #Ref     : 0
% 2.73/1.35  #Sup     : 67
% 2.73/1.35  #Fact    : 0
% 2.73/1.35  #Define  : 0
% 2.73/1.35  #Split   : 9
% 2.73/1.35  #Chain   : 0
% 2.73/1.35  #Close   : 0
% 2.73/1.35  
% 2.73/1.35  Ordering : KBO
% 2.73/1.35  
% 2.73/1.35  Simplification rules
% 2.73/1.35  ----------------------
% 2.73/1.35  #Subsume      : 1
% 2.73/1.35  #Demod        : 37
% 2.73/1.35  #Tautology    : 14
% 2.73/1.35  #SimpNegUnit  : 8
% 2.73/1.35  #BackRed      : 0
% 2.73/1.35  
% 2.73/1.35  #Partial instantiations: 0
% 2.73/1.35  #Strategies tried      : 1
% 2.73/1.35  
% 2.73/1.35  Timing (in seconds)
% 2.73/1.35  ----------------------
% 2.73/1.36  Preprocessing        : 0.30
% 2.73/1.36  Parsing              : 0.17
% 2.73/1.36  CNF conversion       : 0.02
% 2.73/1.36  Main loop            : 0.28
% 2.73/1.36  Inferencing          : 0.12
% 2.73/1.36  Reduction            : 0.07
% 2.73/1.36  Demodulation         : 0.05
% 2.73/1.36  BG Simplification    : 0.02
% 2.73/1.36  Subsumption          : 0.05
% 2.73/1.36  Abstraction          : 0.01
% 2.73/1.36  MUC search           : 0.00
% 2.73/1.36  Cooper               : 0.00
% 2.73/1.36  Total                : 0.63
% 2.73/1.36  Index Insertion      : 0.00
% 2.73/1.36  Index Deletion       : 0.00
% 2.73/1.36  Index Matching       : 0.00
% 2.73/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
