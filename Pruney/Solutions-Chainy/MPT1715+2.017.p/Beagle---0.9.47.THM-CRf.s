%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:39 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 228 expanded)
%              Number of leaves         :   28 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 829 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_350,plain,(
    ! [B_114,A_115] :
      ( l1_pre_topc(B_114)
      | ~ m1_pre_topc(B_114,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_356,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_350])).

tff(c_366,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_356])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_359,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_350])).

tff(c_369,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_359])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_265,plain,(
    ! [B_96,A_97] :
      ( l1_pre_topc(B_96)
      | ~ m1_pre_topc(B_96,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_277,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_265])).

tff(c_287,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_277])).

tff(c_271,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_265])).

tff(c_281,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_271])).

tff(c_51,plain,(
    ! [B_34,A_35] :
      ( l1_pre_topc(B_34)
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_57,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_67,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_57])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_73,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63])).

tff(c_26,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_49,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_91,plain,(
    ! [B_45,A_46] :
      ( r1_tsep_1(B_45,A_46)
      | ~ r1_tsep_1(A_46,B_45)
      | ~ l1_struct_0(B_45)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_91])).

tff(c_95,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_98,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_98])).

tff(c_103,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_108,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_108])).

tff(c_114,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_104,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_113,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_138,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(u1_struct_0(B_50),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(u1_struct_0(B_50),u1_struct_0(A_51))
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_138,c_8])).

tff(c_143,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(u1_struct_0(A_52),u1_struct_0(B_53))
      | ~ r1_tsep_1(A_52,B_53)
      | ~ l1_struct_0(B_53)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(u1_struct_0(A_62),u1_struct_0(B_63)) = u1_struct_0(A_62)
      | ~ r1_tsep_1(A_62,B_63)
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [A_75,A_76,B_77] :
      ( r1_xboole_0(A_75,u1_struct_0(A_76))
      | ~ r1_tarski(A_75,u1_struct_0(B_77))
      | ~ r1_tsep_1(A_76,B_77)
      | ~ l1_struct_0(B_77)
      | ~ l1_struct_0(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_6])).

tff(c_204,plain,(
    ! [B_86,A_87,A_88] :
      ( r1_xboole_0(u1_struct_0(B_86),u1_struct_0(A_87))
      | ~ r1_tsep_1(A_87,A_88)
      | ~ l1_struct_0(A_88)
      | ~ l1_struct_0(A_87)
      | ~ m1_pre_topc(B_86,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_142,c_192])).

tff(c_206,plain,(
    ! [B_86] :
      ( r1_xboole_0(u1_struct_0(B_86),u1_struct_0('#skF_4'))
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(B_86,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_113,c_204])).

tff(c_215,plain,(
    ! [B_89] :
      ( r1_xboole_0(u1_struct_0(B_89),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_89,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_114,c_104,c_206])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( r1_tsep_1(A_12,B_14)
      | ~ r1_xboole_0(u1_struct_0(A_12),u1_struct_0(B_14))
      | ~ l1_struct_0(B_14)
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_218,plain,(
    ! [B_89] :
      ( r1_tsep_1(B_89,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(B_89)
      | ~ m1_pre_topc(B_89,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_215,c_16])).

tff(c_237,plain,(
    ! [B_91] :
      ( r1_tsep_1(B_91,'#skF_4')
      | ~ l1_struct_0(B_91)
      | ~ m1_pre_topc(B_91,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_218])).

tff(c_24,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_244,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_237,c_48])).

tff(c_253,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_244])).

tff(c_256,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_256])).

tff(c_262,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_261,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_322,plain,(
    ! [B_108,A_109] :
      ( r1_tsep_1(B_108,A_109)
      | ~ r1_tsep_1(A_109,B_108)
      | ~ l1_struct_0(B_108)
      | ~ l1_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_324,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_261,c_322])).

tff(c_327,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_324])).

tff(c_328,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_331,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_328])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_331])).

tff(c_336,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_340,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_336])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_340])).

tff(c_345,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_346,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_407,plain,(
    ! [B_126,A_127] :
      ( r1_tsep_1(B_126,A_127)
      | ~ r1_tsep_1(A_127,B_126)
      | ~ l1_struct_0(B_126)
      | ~ l1_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_411,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_346,c_407])).

tff(c_415,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_411])).

tff(c_416,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_419,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_416])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_419])).

tff(c_424,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_428,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_424])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:04:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.33  
% 2.35/1.33  %Foreground sorts:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Background operators:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Foreground operators:
% 2.35/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.35/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.35/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.35/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.35/1.33  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.35/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.35/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.33  
% 2.66/1.35  tff(f_110, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 2.66/1.35  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.66/1.35  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.66/1.35  tff(f_65, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.66/1.35  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.66/1.35  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.66/1.35  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.66/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.66/1.35  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.66/1.35  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_350, plain, (![B_114, A_115]: (l1_pre_topc(B_114) | ~m1_pre_topc(B_114, A_115) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.35  tff(c_356, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_350])).
% 2.66/1.35  tff(c_366, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_356])).
% 2.66/1.35  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.35  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_359, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_350])).
% 2.66/1.35  tff(c_369, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_359])).
% 2.66/1.35  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_265, plain, (![B_96, A_97]: (l1_pre_topc(B_96) | ~m1_pre_topc(B_96, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.35  tff(c_277, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_265])).
% 2.66/1.35  tff(c_287, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_277])).
% 2.66/1.35  tff(c_271, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_265])).
% 2.66/1.35  tff(c_281, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_271])).
% 2.66/1.35  tff(c_51, plain, (![B_34, A_35]: (l1_pre_topc(B_34) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.35  tff(c_60, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_51])).
% 2.66/1.35  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 2.66/1.35  tff(c_28, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_57, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.66/1.35  tff(c_67, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_57])).
% 2.66/1.35  tff(c_63, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.66/1.35  tff(c_73, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63])).
% 2.66/1.35  tff(c_26, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_49, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.66/1.35  tff(c_91, plain, (![B_45, A_46]: (r1_tsep_1(B_45, A_46) | ~r1_tsep_1(A_46, B_45) | ~l1_struct_0(B_45) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.66/1.35  tff(c_94, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_49, c_91])).
% 2.66/1.35  tff(c_95, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 2.66/1.35  tff(c_98, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_95])).
% 2.66/1.35  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_98])).
% 2.66/1.35  tff(c_103, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 2.66/1.35  tff(c_105, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_103])).
% 2.66/1.35  tff(c_108, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.66/1.35  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_108])).
% 2.66/1.35  tff(c_114, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_103])).
% 2.66/1.35  tff(c_104, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 2.66/1.35  tff(c_113, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.66/1.35  tff(c_138, plain, (![B_50, A_51]: (m1_subset_1(u1_struct_0(B_50), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.35  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.35  tff(c_142, plain, (![B_50, A_51]: (r1_tarski(u1_struct_0(B_50), u1_struct_0(A_51)) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_138, c_8])).
% 2.66/1.35  tff(c_143, plain, (![A_52, B_53]: (r1_xboole_0(u1_struct_0(A_52), u1_struct_0(B_53)) | ~r1_tsep_1(A_52, B_53) | ~l1_struct_0(B_53) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.35  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.35  tff(c_161, plain, (![A_62, B_63]: (k4_xboole_0(u1_struct_0(A_62), u1_struct_0(B_63))=u1_struct_0(A_62) | ~r1_tsep_1(A_62, B_63) | ~l1_struct_0(B_63) | ~l1_struct_0(A_62))), inference(resolution, [status(thm)], [c_143, c_2])).
% 2.66/1.35  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.35  tff(c_192, plain, (![A_75, A_76, B_77]: (r1_xboole_0(A_75, u1_struct_0(A_76)) | ~r1_tarski(A_75, u1_struct_0(B_77)) | ~r1_tsep_1(A_76, B_77) | ~l1_struct_0(B_77) | ~l1_struct_0(A_76))), inference(superposition, [status(thm), theory('equality')], [c_161, c_6])).
% 2.66/1.35  tff(c_204, plain, (![B_86, A_87, A_88]: (r1_xboole_0(u1_struct_0(B_86), u1_struct_0(A_87)) | ~r1_tsep_1(A_87, A_88) | ~l1_struct_0(A_88) | ~l1_struct_0(A_87) | ~m1_pre_topc(B_86, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_142, c_192])).
% 2.66/1.35  tff(c_206, plain, (![B_86]: (r1_xboole_0(u1_struct_0(B_86), u1_struct_0('#skF_4')) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4') | ~m1_pre_topc(B_86, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_113, c_204])).
% 2.66/1.35  tff(c_215, plain, (![B_89]: (r1_xboole_0(u1_struct_0(B_89), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_89, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_114, c_104, c_206])).
% 2.66/1.35  tff(c_16, plain, (![A_12, B_14]: (r1_tsep_1(A_12, B_14) | ~r1_xboole_0(u1_struct_0(A_12), u1_struct_0(B_14)) | ~l1_struct_0(B_14) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.35  tff(c_218, plain, (![B_89]: (r1_tsep_1(B_89, '#skF_4') | ~l1_struct_0('#skF_4') | ~l1_struct_0(B_89) | ~m1_pre_topc(B_89, '#skF_3'))), inference(resolution, [status(thm)], [c_215, c_16])).
% 2.66/1.35  tff(c_237, plain, (![B_91]: (r1_tsep_1(B_91, '#skF_4') | ~l1_struct_0(B_91) | ~m1_pre_topc(B_91, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_218])).
% 2.66/1.35  tff(c_24, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.35  tff(c_48, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.66/1.35  tff(c_244, plain, (~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_237, c_48])).
% 2.66/1.35  tff(c_253, plain, (~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_244])).
% 2.66/1.35  tff(c_256, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_253])).
% 2.66/1.35  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_256])).
% 2.66/1.35  tff(c_262, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.66/1.35  tff(c_261, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.66/1.35  tff(c_322, plain, (![B_108, A_109]: (r1_tsep_1(B_108, A_109) | ~r1_tsep_1(A_109, B_108) | ~l1_struct_0(B_108) | ~l1_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.66/1.35  tff(c_324, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_261, c_322])).
% 2.66/1.35  tff(c_327, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_262, c_324])).
% 2.66/1.35  tff(c_328, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_327])).
% 2.66/1.35  tff(c_331, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_328])).
% 2.66/1.35  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_331])).
% 2.66/1.35  tff(c_336, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_327])).
% 2.66/1.35  tff(c_340, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_336])).
% 2.66/1.35  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_340])).
% 2.66/1.35  tff(c_345, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.66/1.35  tff(c_346, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 2.66/1.35  tff(c_407, plain, (![B_126, A_127]: (r1_tsep_1(B_126, A_127) | ~r1_tsep_1(A_127, B_126) | ~l1_struct_0(B_126) | ~l1_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.66/1.35  tff(c_411, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_346, c_407])).
% 2.66/1.35  tff(c_415, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_345, c_411])).
% 2.66/1.35  tff(c_416, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_415])).
% 2.66/1.35  tff(c_419, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_416])).
% 2.66/1.35  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_419])).
% 2.66/1.35  tff(c_424, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_415])).
% 2.66/1.35  tff(c_428, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_424])).
% 2.66/1.35  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_428])).
% 2.66/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  Inference rules
% 2.66/1.35  ----------------------
% 2.66/1.35  #Ref     : 0
% 2.66/1.35  #Sup     : 74
% 2.66/1.35  #Fact    : 0
% 2.66/1.35  #Define  : 0
% 2.66/1.35  #Split   : 7
% 2.66/1.35  #Chain   : 0
% 2.66/1.35  #Close   : 0
% 2.66/1.35  
% 2.66/1.35  Ordering : KBO
% 2.66/1.35  
% 2.66/1.35  Simplification rules
% 2.66/1.35  ----------------------
% 2.66/1.35  #Subsume      : 1
% 2.66/1.35  #Demod        : 34
% 2.66/1.35  #Tautology    : 20
% 2.66/1.35  #SimpNegUnit  : 2
% 2.66/1.35  #BackRed      : 0
% 2.66/1.35  
% 2.66/1.35  #Partial instantiations: 0
% 2.66/1.35  #Strategies tried      : 1
% 2.66/1.35  
% 2.66/1.35  Timing (in seconds)
% 2.66/1.35  ----------------------
% 2.66/1.35  Preprocessing        : 0.30
% 2.66/1.35  Parsing              : 0.17
% 2.66/1.35  CNF conversion       : 0.02
% 2.66/1.35  Main loop            : 0.28
% 2.66/1.35  Inferencing          : 0.11
% 2.66/1.35  Reduction            : 0.07
% 2.66/1.35  Demodulation         : 0.05
% 2.66/1.35  BG Simplification    : 0.02
% 2.66/1.35  Subsumption          : 0.05
% 2.66/1.35  Abstraction          : 0.01
% 2.66/1.35  MUC search           : 0.00
% 2.66/1.35  Cooper               : 0.00
% 2.66/1.35  Total                : 0.63
% 2.66/1.35  Index Insertion      : 0.00
% 2.66/1.35  Index Deletion       : 0.00
% 2.66/1.35  Index Matching       : 0.00
% 2.66/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
