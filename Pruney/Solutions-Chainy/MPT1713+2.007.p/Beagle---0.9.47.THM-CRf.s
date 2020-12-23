%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 385 expanded)
%              Number of leaves         :   35 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  178 (1138 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_107,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_107])).

tff(c_122,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_113])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_110,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_119,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_110])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    ! [B_29,A_7] :
      ( r1_tarski(k2_struct_0(B_29),k2_struct_0(A_7))
      | ~ m1_pre_topc(B_29,A_7)
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_73,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_127,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_77])).

tff(c_44,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_44])).

tff(c_140,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_137])).

tff(c_157,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_160,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_160])).

tff(c_165,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_131,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_77])).

tff(c_152,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_44])).

tff(c_155,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_152])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_175,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_167])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_175])).

tff(c_181,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_52,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_71,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_192,plain,(
    ! [B_70,A_71] :
      ( r1_tsep_1(B_70,A_71)
      | ~ r1_tsep_1(A_71,B_70)
      | ~ l1_struct_0(B_70)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_194,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_192])).

tff(c_197,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_181,c_194])).

tff(c_308,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(u1_struct_0(A_83),u1_struct_0(B_84))
      | ~ r1_tsep_1(A_83,B_84)
      | ~ l1_struct_0(B_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_316,plain,(
    ! [B_84] :
      ( r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_84))
      | ~ r1_tsep_1('#skF_6',B_84)
      | ~ l1_struct_0(B_84)
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_308])).

tff(c_412,plain,(
    ! [B_89] :
      ( r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_89))
      | ~ r1_tsep_1('#skF_6',B_89)
      | ~ l1_struct_0(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_316])).

tff(c_423,plain,
    ( r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_412])).

tff(c_433,plain,(
    r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_197,c_423])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(C_5,A_3)
      | v1_xboole_0(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_561,plain,(
    ! [C_99] :
      ( ~ r1_tarski(C_99,k2_struct_0('#skF_5'))
      | ~ r1_tarski(C_99,k2_struct_0('#skF_6'))
      | v1_xboole_0(C_99) ) ),
    inference(resolution,[status(thm)],[c_433,c_8])).

tff(c_569,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_561])).

tff(c_575,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_569])).

tff(c_578,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_119,c_54,c_578])).

tff(c_584,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_600,plain,(
    ! [B_103,A_104] :
      ( l1_pre_topc(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_606,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_600])).

tff(c_615,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_606])).

tff(c_586,plain,(
    ! [A_101] :
      ( u1_struct_0(A_101) = k2_struct_0(A_101)
      | ~ l1_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_590,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_40,c_586])).

tff(c_637,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_615,c_590])).

tff(c_648,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_44])).

tff(c_651,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_648])).

tff(c_676,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_686,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_676])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_686])).

tff(c_692,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_603,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_600])).

tff(c_612,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_603])).

tff(c_633,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_612,c_590])).

tff(c_671,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_44])).

tff(c_674,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_671])).

tff(c_698,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_701,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_698])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_701])).

tff(c_707,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_583,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_720,plain,(
    ! [B_110,A_111] :
      ( r1_tsep_1(B_110,A_111)
      | ~ r1_tsep_1(A_111,B_110)
      | ~ l1_struct_0(B_110)
      | ~ l1_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_722,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_583,c_720])).

tff(c_725,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_707,c_722])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_584,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.48  
% 3.00/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.48  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.00/1.48  
% 3.00/1.48  %Foreground sorts:
% 3.00/1.48  
% 3.00/1.48  
% 3.00/1.48  %Background operators:
% 3.00/1.48  
% 3.00/1.48  
% 3.00/1.48  %Foreground operators:
% 3.00/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.00/1.48  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.00/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.00/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.00/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.00/1.48  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.00/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.00/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.00/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.48  
% 3.00/1.50  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 3.00/1.50  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.00/1.50  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.00/1.50  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.00/1.50  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.00/1.50  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.00/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.50  tff(f_102, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.00/1.50  tff(f_94, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.00/1.50  tff(f_41, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 3.00/1.50  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_56, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_107, plain, (![B_66, A_67]: (l1_pre_topc(B_66) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.50  tff(c_113, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_107])).
% 3.00/1.50  tff(c_122, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_113])).
% 3.00/1.50  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_110, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_107])).
% 3.00/1.50  tff(c_119, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_110])).
% 3.00/1.50  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_30, plain, (![B_29, A_7]: (r1_tarski(k2_struct_0(B_29), k2_struct_0(A_7)) | ~m1_pre_topc(B_29, A_7) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_40, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.50  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_73, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.50  tff(c_77, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_40, c_73])).
% 3.00/1.50  tff(c_127, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_119, c_77])).
% 3.00/1.50  tff(c_44, plain, (![A_51]: (~v1_xboole_0(u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.50  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_127, c_44])).
% 3.00/1.50  tff(c_140, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_137])).
% 3.00/1.50  tff(c_157, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_140])).
% 3.00/1.50  tff(c_160, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_157])).
% 3.00/1.50  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_160])).
% 3.00/1.50  tff(c_165, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_140])).
% 3.00/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.50  tff(c_166, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_140])).
% 3.00/1.50  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_131, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_122, c_77])).
% 3.00/1.50  tff(c_152, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_131, c_44])).
% 3.00/1.50  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_152])).
% 3.00/1.50  tff(c_167, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_155])).
% 3.00/1.50  tff(c_175, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_167])).
% 3.00/1.50  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_175])).
% 3.00/1.50  tff(c_181, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_155])).
% 3.00/1.50  tff(c_52, plain, (r1_tsep_1('#skF_6', '#skF_5') | r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.00/1.50  tff(c_71, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 3.00/1.50  tff(c_192, plain, (![B_70, A_71]: (r1_tsep_1(B_70, A_71) | ~r1_tsep_1(A_71, B_70) | ~l1_struct_0(B_70) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.50  tff(c_194, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_71, c_192])).
% 3.00/1.50  tff(c_197, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_181, c_194])).
% 3.00/1.50  tff(c_308, plain, (![A_83, B_84]: (r1_xboole_0(u1_struct_0(A_83), u1_struct_0(B_84)) | ~r1_tsep_1(A_83, B_84) | ~l1_struct_0(B_84) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.50  tff(c_316, plain, (![B_84]: (r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_84)) | ~r1_tsep_1('#skF_6', B_84) | ~l1_struct_0(B_84) | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_308])).
% 3.00/1.50  tff(c_412, plain, (![B_89]: (r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_89)) | ~r1_tsep_1('#skF_6', B_89) | ~l1_struct_0(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_316])).
% 3.00/1.50  tff(c_423, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_127, c_412])).
% 3.00/1.50  tff(c_433, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_197, c_423])).
% 3.00/1.50  tff(c_8, plain, (![A_3, B_4, C_5]: (~r1_xboole_0(A_3, B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(C_5, A_3) | v1_xboole_0(C_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.50  tff(c_561, plain, (![C_99]: (~r1_tarski(C_99, k2_struct_0('#skF_5')) | ~r1_tarski(C_99, k2_struct_0('#skF_6')) | v1_xboole_0(C_99))), inference(resolution, [status(thm)], [c_433, c_8])).
% 3.00/1.50  tff(c_569, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_6, c_561])).
% 3.00/1.50  tff(c_575, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_165, c_569])).
% 3.00/1.50  tff(c_578, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_30, c_575])).
% 3.00/1.50  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_119, c_54, c_578])).
% 3.00/1.50  tff(c_584, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 3.00/1.50  tff(c_600, plain, (![B_103, A_104]: (l1_pre_topc(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.50  tff(c_606, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_600])).
% 3.00/1.50  tff(c_615, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_606])).
% 3.00/1.50  tff(c_586, plain, (![A_101]: (u1_struct_0(A_101)=k2_struct_0(A_101) | ~l1_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.50  tff(c_590, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_40, c_586])).
% 3.00/1.50  tff(c_637, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_615, c_590])).
% 3.00/1.50  tff(c_648, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_637, c_44])).
% 3.00/1.50  tff(c_651, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_648])).
% 3.00/1.50  tff(c_676, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_651])).
% 3.00/1.50  tff(c_686, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_676])).
% 3.00/1.50  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_615, c_686])).
% 3.00/1.50  tff(c_692, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_651])).
% 3.00/1.50  tff(c_603, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_600])).
% 3.00/1.50  tff(c_612, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_603])).
% 3.00/1.50  tff(c_633, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_612, c_590])).
% 3.00/1.50  tff(c_671, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_633, c_44])).
% 3.00/1.50  tff(c_674, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_671])).
% 3.00/1.50  tff(c_698, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_674])).
% 3.00/1.50  tff(c_701, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_698])).
% 3.00/1.50  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_612, c_701])).
% 3.00/1.50  tff(c_707, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_674])).
% 3.00/1.50  tff(c_583, plain, (r1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.00/1.50  tff(c_720, plain, (![B_110, A_111]: (r1_tsep_1(B_110, A_111) | ~r1_tsep_1(A_111, B_110) | ~l1_struct_0(B_110) | ~l1_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.50  tff(c_722, plain, (r1_tsep_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_583, c_720])).
% 3.00/1.50  tff(c_725, plain, (r1_tsep_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_707, c_722])).
% 3.00/1.50  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_584, c_725])).
% 3.00/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  Inference rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Ref     : 0
% 3.00/1.50  #Sup     : 124
% 3.00/1.50  #Fact    : 0
% 3.00/1.50  #Define  : 0
% 3.00/1.50  #Split   : 15
% 3.00/1.50  #Chain   : 0
% 3.00/1.50  #Close   : 0
% 3.00/1.50  
% 3.00/1.50  Ordering : KBO
% 3.00/1.50  
% 3.00/1.50  Simplification rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Subsume      : 14
% 3.00/1.50  #Demod        : 99
% 3.00/1.50  #Tautology    : 41
% 3.00/1.50  #SimpNegUnit  : 27
% 3.00/1.50  #BackRed      : 0
% 3.00/1.50  
% 3.00/1.50  #Partial instantiations: 0
% 3.00/1.50  #Strategies tried      : 1
% 3.00/1.50  
% 3.00/1.50  Timing (in seconds)
% 3.00/1.50  ----------------------
% 3.00/1.50  Preprocessing        : 0.37
% 3.00/1.50  Parsing              : 0.18
% 3.00/1.50  CNF conversion       : 0.03
% 3.00/1.50  Main loop            : 0.31
% 3.00/1.50  Inferencing          : 0.10
% 3.00/1.50  Reduction            : 0.10
% 3.00/1.50  Demodulation         : 0.07
% 3.00/1.50  BG Simplification    : 0.02
% 3.00/1.50  Subsumption          : 0.06
% 3.00/1.50  Abstraction          : 0.02
% 3.00/1.50  MUC search           : 0.00
% 3.00/1.50  Cooper               : 0.00
% 3.00/1.50  Total                : 0.72
% 3.00/1.50  Index Insertion      : 0.00
% 3.00/1.50  Index Deletion       : 0.00
% 3.00/1.50  Index Matching       : 0.00
% 3.00/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
