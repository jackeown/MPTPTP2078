%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:38 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 358 expanded)
%              Number of leaves         :   33 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  197 (1273 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_50,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_841,plain,(
    ! [B_118,A_119] :
      ( l1_pre_topc(B_118)
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_844,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_841])).

tff(c_856,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_844])).

tff(c_34,plain,(
    ! [A_45] :
      ( l1_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_853,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_841])).

tff(c_863,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_853])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_860,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_841])).

tff(c_864,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_860])).

tff(c_878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_864])).

tff(c_879,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_720,plain,(
    ! [B_107,A_108] :
      ( l1_pre_topc(B_107)
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_732,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_720])).

tff(c_742,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_732])).

tff(c_723,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_720])).

tff(c_735,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_723])).

tff(c_84,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_106,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_96])).

tff(c_103,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_107,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_107])).

tff(c_122,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_24,plain,(
    ! [B_27,A_5] :
      ( r1_tarski(k2_struct_0(B_27),k2_struct_0(A_5))
      | ~ m1_pre_topc(B_27,A_5)
      | ~ l1_pre_topc(B_27)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_151,plain,(
    ! [B_73,A_74] :
      ( r1_tsep_1(B_73,A_74)
      | ~ r1_tsep_1(A_74,B_73)
      | ~ l1_struct_0(B_73)
      | ~ l1_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_154,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_151])).

tff(c_155,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_183,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_183])).

tff(c_189,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_69,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_132,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_106,c_73])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_84])).

tff(c_99,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_87])).

tff(c_188,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_195,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_198,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_198])).

tff(c_204,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_127,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_99,c_73])).

tff(c_301,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(u1_struct_0(A_83),u1_struct_0(B_84))
      | ~ r1_tsep_1(A_83,B_84)
      | ~ l1_struct_0(B_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_312,plain,(
    ! [A_83] :
      ( r1_xboole_0(u1_struct_0(A_83),k2_struct_0('#skF_7'))
      | ~ r1_tsep_1(A_83,'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_301])).

tff(c_500,plain,(
    ! [A_95] :
      ( r1_xboole_0(u1_struct_0(A_95),k2_struct_0('#skF_7'))
      | ~ r1_tsep_1(A_95,'#skF_7')
      | ~ l1_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_312])).

tff(c_508,plain,
    ( r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'))
    | ~ r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_500])).

tff(c_520,plain,(
    r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_74,c_508])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_547,plain,(
    ! [A_1] :
      ( r1_xboole_0(A_1,k2_struct_0('#skF_7'))
      | ~ r1_tarski(A_1,k2_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_520,c_2])).

tff(c_44,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_68,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_137,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_73])).

tff(c_215,plain,(
    ! [A_77,B_78] :
      ( r1_tsep_1(A_77,B_78)
      | ~ r1_xboole_0(u1_struct_0(A_77),u1_struct_0(B_78))
      | ~ l1_struct_0(B_78)
      | ~ l1_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_221,plain,(
    ! [A_77] :
      ( r1_tsep_1(A_77,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_77),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_215])).

tff(c_632,plain,(
    ! [A_102] :
      ( r1_tsep_1(A_102,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_102),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_221])).

tff(c_647,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_632])).

tff(c_658,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_647])).

tff(c_683,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_658])).

tff(c_686,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_683])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_686])).

tff(c_691,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_658])).

tff(c_701,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_547,c_691])).

tff(c_704,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_701])).

tff(c_708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_122,c_48,c_704])).

tff(c_710,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_709,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_770,plain,(
    ! [B_112,A_113] :
      ( r1_tsep_1(B_112,A_113)
      | ~ r1_tsep_1(A_113,B_112)
      | ~ l1_struct_0(B_112)
      | ~ l1_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_772,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_709,c_770])).

tff(c_775,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_772])).

tff(c_801,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_804,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_801])).

tff(c_808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_804])).

tff(c_809,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_819,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_809])).

tff(c_823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_819])).

tff(c_824,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_825,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_908,plain,(
    ! [B_123,A_124] :
      ( r1_tsep_1(B_123,A_124)
      | ~ r1_tsep_1(A_124,B_123)
      | ~ l1_struct_0(B_123)
      | ~ l1_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_912,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_825,c_908])).

tff(c_916,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_824,c_912])).

tff(c_917,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_916])).

tff(c_945,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_917])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_945])).

tff(c_950,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_916])).

tff(c_954,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_950])).

tff(c_958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:05:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.50  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.20/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.20/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.20/1.50  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.20/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.20/1.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.20/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.50  
% 3.20/1.52  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 3.20/1.52  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.20/1.52  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.52  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.20/1.52  tff(f_84, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.20/1.52  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.52  tff(f_76, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.20/1.52  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.20/1.52  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_50, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_841, plain, (![B_118, A_119]: (l1_pre_topc(B_118) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.52  tff(c_844, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_841])).
% 3.20/1.52  tff(c_856, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_844])).
% 3.20/1.52  tff(c_34, plain, (![A_45]: (l1_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.52  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_853, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_841])).
% 3.20/1.52  tff(c_863, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_853])).
% 3.20/1.52  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_860, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_841])).
% 3.20/1.52  tff(c_864, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_860])).
% 3.20/1.52  tff(c_878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_863, c_864])).
% 3.20/1.52  tff(c_879, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_860])).
% 3.20/1.52  tff(c_720, plain, (![B_107, A_108]: (l1_pre_topc(B_107) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.52  tff(c_732, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_720])).
% 3.20/1.52  tff(c_742, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_732])).
% 3.20/1.52  tff(c_723, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_720])).
% 3.20/1.52  tff(c_735, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_723])).
% 3.20/1.52  tff(c_84, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.52  tff(c_96, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_84])).
% 3.20/1.52  tff(c_106, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_96])).
% 3.20/1.52  tff(c_103, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_84])).
% 3.20/1.52  tff(c_107, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_103])).
% 3.20/1.52  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_107])).
% 3.20/1.52  tff(c_122, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_103])).
% 3.20/1.52  tff(c_24, plain, (![B_27, A_5]: (r1_tarski(k2_struct_0(B_27), k2_struct_0(A_5)) | ~m1_pre_topc(B_27, A_5) | ~l1_pre_topc(B_27) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.20/1.52  tff(c_46, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_74, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 3.20/1.52  tff(c_151, plain, (![B_73, A_74]: (r1_tsep_1(B_73, A_74) | ~r1_tsep_1(A_74, B_73) | ~l1_struct_0(B_73) | ~l1_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.52  tff(c_154, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_151])).
% 3.20/1.52  tff(c_155, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_154])).
% 3.20/1.52  tff(c_183, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_34, c_155])).
% 3.20/1.52  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_183])).
% 3.20/1.52  tff(c_189, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_154])).
% 3.20/1.52  tff(c_69, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.52  tff(c_73, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_34, c_69])).
% 3.20/1.52  tff(c_132, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_106, c_73])).
% 3.20/1.52  tff(c_87, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_84])).
% 3.20/1.52  tff(c_99, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_87])).
% 3.20/1.52  tff(c_188, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_154])).
% 3.20/1.52  tff(c_195, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_188])).
% 3.20/1.52  tff(c_198, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_34, c_195])).
% 3.20/1.52  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_198])).
% 3.20/1.52  tff(c_204, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_188])).
% 3.20/1.52  tff(c_127, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_99, c_73])).
% 3.20/1.52  tff(c_301, plain, (![A_83, B_84]: (r1_xboole_0(u1_struct_0(A_83), u1_struct_0(B_84)) | ~r1_tsep_1(A_83, B_84) | ~l1_struct_0(B_84) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.52  tff(c_312, plain, (![A_83]: (r1_xboole_0(u1_struct_0(A_83), k2_struct_0('#skF_7')) | ~r1_tsep_1(A_83, '#skF_7') | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_83))), inference(superposition, [status(thm), theory('equality')], [c_127, c_301])).
% 3.20/1.52  tff(c_500, plain, (![A_95]: (r1_xboole_0(u1_struct_0(A_95), k2_struct_0('#skF_7')) | ~r1_tsep_1(A_95, '#skF_7') | ~l1_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_312])).
% 3.20/1.52  tff(c_508, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7')) | ~r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_132, c_500])).
% 3.20/1.52  tff(c_520, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_74, c_508])).
% 3.20/1.52  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.52  tff(c_547, plain, (![A_1]: (r1_xboole_0(A_1, k2_struct_0('#skF_7')) | ~r1_tarski(A_1, k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_520, c_2])).
% 3.20/1.52  tff(c_44, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.20/1.52  tff(c_68, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 3.20/1.52  tff(c_137, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_122, c_73])).
% 3.20/1.52  tff(c_215, plain, (![A_77, B_78]: (r1_tsep_1(A_77, B_78) | ~r1_xboole_0(u1_struct_0(A_77), u1_struct_0(B_78)) | ~l1_struct_0(B_78) | ~l1_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.52  tff(c_221, plain, (![A_77]: (r1_tsep_1(A_77, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_77), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_77))), inference(superposition, [status(thm), theory('equality')], [c_127, c_215])).
% 3.20/1.52  tff(c_632, plain, (![A_102]: (r1_tsep_1(A_102, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_102), k2_struct_0('#skF_7')) | ~l1_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_221])).
% 3.20/1.52  tff(c_647, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_137, c_632])).
% 3.20/1.52  tff(c_658, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_647])).
% 3.20/1.52  tff(c_683, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_658])).
% 3.20/1.52  tff(c_686, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_34, c_683])).
% 3.20/1.52  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_686])).
% 3.20/1.52  tff(c_691, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_658])).
% 3.20/1.52  tff(c_701, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_547, c_691])).
% 3.20/1.52  tff(c_704, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_24, c_701])).
% 3.20/1.52  tff(c_708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_122, c_48, c_704])).
% 3.20/1.52  tff(c_710, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 3.20/1.52  tff(c_709, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 3.20/1.52  tff(c_770, plain, (![B_112, A_113]: (r1_tsep_1(B_112, A_113) | ~r1_tsep_1(A_113, B_112) | ~l1_struct_0(B_112) | ~l1_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.52  tff(c_772, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_709, c_770])).
% 3.20/1.52  tff(c_775, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_710, c_772])).
% 3.20/1.52  tff(c_801, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_775])).
% 3.20/1.52  tff(c_804, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_34, c_801])).
% 3.20/1.52  tff(c_808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_735, c_804])).
% 3.20/1.52  tff(c_809, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_775])).
% 3.20/1.52  tff(c_819, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_34, c_809])).
% 3.20/1.52  tff(c_823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_742, c_819])).
% 3.20/1.52  tff(c_824, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 3.20/1.52  tff(c_825, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 3.20/1.52  tff(c_908, plain, (![B_123, A_124]: (r1_tsep_1(B_123, A_124) | ~r1_tsep_1(A_124, B_123) | ~l1_struct_0(B_123) | ~l1_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.52  tff(c_912, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_825, c_908])).
% 3.20/1.52  tff(c_916, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_824, c_912])).
% 3.20/1.52  tff(c_917, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_916])).
% 3.20/1.52  tff(c_945, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_34, c_917])).
% 3.20/1.52  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_879, c_945])).
% 3.20/1.52  tff(c_950, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_916])).
% 3.20/1.52  tff(c_954, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_34, c_950])).
% 3.20/1.52  tff(c_958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_856, c_954])).
% 3.20/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  Inference rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Ref     : 0
% 3.20/1.52  #Sup     : 194
% 3.20/1.52  #Fact    : 0
% 3.20/1.52  #Define  : 0
% 3.20/1.52  #Split   : 19
% 3.20/1.52  #Chain   : 0
% 3.20/1.52  #Close   : 0
% 3.20/1.52  
% 3.20/1.52  Ordering : KBO
% 3.20/1.52  
% 3.20/1.52  Simplification rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Subsume      : 12
% 3.20/1.52  #Demod        : 107
% 3.20/1.52  #Tautology    : 48
% 3.20/1.52  #SimpNegUnit  : 18
% 3.20/1.52  #BackRed      : 0
% 3.20/1.52  
% 3.20/1.52  #Partial instantiations: 0
% 3.20/1.52  #Strategies tried      : 1
% 3.20/1.52  
% 3.20/1.52  Timing (in seconds)
% 3.20/1.52  ----------------------
% 3.42/1.52  Preprocessing        : 0.34
% 3.42/1.52  Parsing              : 0.17
% 3.42/1.52  CNF conversion       : 0.03
% 3.42/1.52  Main loop            : 0.36
% 3.42/1.52  Inferencing          : 0.12
% 3.42/1.52  Reduction            : 0.12
% 3.42/1.52  Demodulation         : 0.08
% 3.42/1.52  BG Simplification    : 0.02
% 3.42/1.52  Subsumption          : 0.07
% 3.42/1.52  Abstraction          : 0.02
% 3.42/1.52  MUC search           : 0.00
% 3.42/1.52  Cooper               : 0.00
% 3.42/1.53  Total                : 0.75
% 3.42/1.53  Index Insertion      : 0.00
% 3.42/1.53  Index Deletion       : 0.00
% 3.42/1.53  Index Matching       : 0.00
% 3.42/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
