%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:38 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 606 expanded)
%              Number of leaves         :   35 ( 205 expanded)
%              Depth                    :   13
%              Number of atoms          :  237 (2171 expanded)
%              Number of equality atoms :   10 (  76 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_70,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1020,plain,(
    ! [B_152,A_153] :
      ( l1_pre_topc(B_152)
      | ~ m1_pre_topc(B_152,A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1032,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1020])).

tff(c_1042,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1032])).

tff(c_40,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1023,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1020])).

tff(c_1035,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1023])).

tff(c_910,plain,(
    ! [B_135,A_136] :
      ( l1_pre_topc(B_135)
      | ~ m1_pre_topc(B_135,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_913,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_910])).

tff(c_925,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_913])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_916,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_910])).

tff(c_928,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_916])).

tff(c_50,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_80,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_91,plain,(
    ! [B_72,A_73] :
      ( l1_pre_topc(B_72)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_106,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_94])).

tff(c_103,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_113,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_103])).

tff(c_52,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_74,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_142,plain,(
    ! [B_80,A_81] :
      ( r1_tsep_1(B_80,A_81)
      | ~ r1_tsep_1(A_81,B_80)
      | ~ l1_struct_0(B_80)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_145,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_142])).

tff(c_146,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_149,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_149])).

tff(c_154,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_161,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_164,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_164])).

tff(c_170,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_91])).

tff(c_109,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_97])).

tff(c_75,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_121,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_79])).

tff(c_155,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_125,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_79])).

tff(c_190,plain,(
    ! [A_85,B_86] :
      ( r1_tsep_1(A_85,B_86)
      | ~ r1_xboole_0(u1_struct_0(A_85),u1_struct_0(B_86))
      | ~ l1_struct_0(B_86)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_193,plain,(
    ! [B_86] :
      ( r1_tsep_1('#skF_6',B_86)
      | ~ r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_86))
      | ~ l1_struct_0(B_86)
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_190])).

tff(c_444,plain,(
    ! [B_100] :
      ( r1_tsep_1('#skF_6',B_100)
      | ~ r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_100))
      | ~ l1_struct_0(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_193])).

tff(c_450,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_444])).

tff(c_516,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_519,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_516])).

tff(c_523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_519])).

tff(c_525,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_169,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_117,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_106,c_79])).

tff(c_288,plain,(
    ! [A_91,B_92] :
      ( r1_xboole_0(u1_struct_0(A_91),u1_struct_0(B_92))
      | ~ r1_tsep_1(A_91,B_92)
      | ~ l1_struct_0(B_92)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_306,plain,(
    ! [B_92] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_92))
      | ~ r1_tsep_1('#skF_7',B_92)
      | ~ l1_struct_0(B_92)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_288])).

tff(c_466,plain,(
    ! [B_104] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_104))
      | ~ r1_tsep_1('#skF_7',B_104)
      | ~ l1_struct_0(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_306])).

tff(c_472,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_466])).

tff(c_484,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_169,c_472])).

tff(c_258,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k2_struct_0(B_88),k2_struct_0(A_89))
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_794,plain,(
    ! [B_123,A_124] :
      ( k2_xboole_0(k2_struct_0(B_123),k2_struct_0(A_124)) = k2_struct_0(A_124)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(B_123)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_258,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_841,plain,(
    ! [A_128,B_129,A_130] :
      ( r1_xboole_0(A_128,k2_struct_0(B_129))
      | ~ r1_xboole_0(A_128,k2_struct_0(A_130))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(B_129)
      | ~ l1_pre_topc(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_8])).

tff(c_847,plain,(
    ! [B_129] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0(B_129))
      | ~ m1_pre_topc(B_129,'#skF_6')
      | ~ l1_pre_topc(B_129)
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_484,c_841])).

tff(c_872,plain,(
    ! [B_131] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0(B_131))
      | ~ m1_pre_topc(B_131,'#skF_6')
      | ~ l1_pre_topc(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_847])).

tff(c_475,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_466])).

tff(c_645,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_475])).

tff(c_646,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_205,plain,(
    ! [B_86] :
      ( r1_tsep_1('#skF_7',B_86)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_86))
      | ~ l1_struct_0(B_86)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_190])).

tff(c_329,plain,(
    ! [B_93] :
      ( r1_tsep_1('#skF_7',B_93)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_93))
      | ~ l1_struct_0(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_205])).

tff(c_335,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_329])).

tff(c_651,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_335])).

tff(c_652,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_651])).

tff(c_877,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_872,c_652])).

tff(c_888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_54,c_877])).

tff(c_890,plain,(
    r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_48,plain,(
    ! [B_55,A_54] :
      ( r1_tsep_1(B_55,A_54)
      | ~ r1_tsep_1(A_54,B_55)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_892,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_890,c_48])).

tff(c_895,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_525,c_892])).

tff(c_897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_895])).

tff(c_898,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_899,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_961,plain,(
    ! [B_143,A_144] :
      ( r1_tsep_1(B_143,A_144)
      | ~ r1_tsep_1(A_144,B_143)
      | ~ l1_struct_0(B_143)
      | ~ l1_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_963,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_899,c_961])).

tff(c_968,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_898,c_963])).

tff(c_979,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_982,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_979])).

tff(c_986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_982])).

tff(c_987,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_997,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_987])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_997])).

tff(c_1003,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1002,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1071,plain,(
    ! [B_160,A_161] :
      ( r1_tsep_1(B_160,A_161)
      | ~ r1_tsep_1(A_161,B_160)
      | ~ l1_struct_0(B_160)
      | ~ l1_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1073,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1002,c_1071])).

tff(c_1076,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_1073])).

tff(c_1077,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1076])).

tff(c_1080,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_1077])).

tff(c_1084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_1080])).

tff(c_1085,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1076])).

tff(c_1089,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_1085])).

tff(c_1093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_1089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.46  
% 2.96/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.46  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.96/1.46  
% 2.96/1.46  %Foreground sorts:
% 2.96/1.46  
% 2.96/1.46  
% 2.96/1.46  %Background operators:
% 2.96/1.46  
% 2.96/1.46  
% 2.96/1.46  %Foreground operators:
% 2.96/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.96/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.96/1.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.96/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.96/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.96/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.96/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.96/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.96/1.46  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.96/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.96/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.96/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.96/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.46  
% 3.42/1.48  tff(f_136, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 3.42/1.48  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.42/1.48  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.42/1.48  tff(f_98, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.42/1.48  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.42/1.48  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.42/1.48  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.42/1.48  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.42/1.48  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.42/1.48  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_1020, plain, (![B_152, A_153]: (l1_pre_topc(B_152) | ~m1_pre_topc(B_152, A_153) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.42/1.48  tff(c_1032, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1020])).
% 3.42/1.48  tff(c_1042, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1032])).
% 3.42/1.48  tff(c_40, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.48  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_1023, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1020])).
% 3.42/1.48  tff(c_1035, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1023])).
% 3.42/1.48  tff(c_910, plain, (![B_135, A_136]: (l1_pre_topc(B_135) | ~m1_pre_topc(B_135, A_136) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.42/1.48  tff(c_913, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_910])).
% 3.42/1.48  tff(c_925, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_913])).
% 3.42/1.48  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_916, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_910])).
% 3.42/1.48  tff(c_928, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_916])).
% 3.42/1.48  tff(c_50, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_80, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 3.42/1.48  tff(c_91, plain, (![B_72, A_73]: (l1_pre_topc(B_72) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.42/1.48  tff(c_94, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_91])).
% 3.42/1.48  tff(c_106, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_94])).
% 3.42/1.48  tff(c_103, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.42/1.48  tff(c_113, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_103])).
% 3.42/1.48  tff(c_52, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_74, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 3.42/1.48  tff(c_142, plain, (![B_80, A_81]: (r1_tsep_1(B_80, A_81) | ~r1_tsep_1(A_81, B_80) | ~l1_struct_0(B_80) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.48  tff(c_145, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_142])).
% 3.42/1.48  tff(c_146, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_145])).
% 3.42/1.48  tff(c_149, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_146])).
% 3.42/1.48  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_149])).
% 3.42/1.48  tff(c_154, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_145])).
% 3.42/1.48  tff(c_161, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_154])).
% 3.42/1.48  tff(c_164, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_161])).
% 3.42/1.48  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_164])).
% 3.42/1.48  tff(c_170, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_154])).
% 3.42/1.48  tff(c_97, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_91])).
% 3.42/1.48  tff(c_109, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_97])).
% 3.42/1.48  tff(c_75, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.42/1.48  tff(c_79, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.42/1.48  tff(c_121, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_109, c_79])).
% 3.42/1.48  tff(c_155, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_145])).
% 3.42/1.48  tff(c_125, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_113, c_79])).
% 3.42/1.48  tff(c_190, plain, (![A_85, B_86]: (r1_tsep_1(A_85, B_86) | ~r1_xboole_0(u1_struct_0(A_85), u1_struct_0(B_86)) | ~l1_struct_0(B_86) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.48  tff(c_193, plain, (![B_86]: (r1_tsep_1('#skF_6', B_86) | ~r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_86)) | ~l1_struct_0(B_86) | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_190])).
% 3.42/1.48  tff(c_444, plain, (![B_100]: (r1_tsep_1('#skF_6', B_100) | ~r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_100)) | ~l1_struct_0(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_193])).
% 3.42/1.48  tff(c_450, plain, (r1_tsep_1('#skF_6', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_121, c_444])).
% 3.42/1.48  tff(c_516, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_450])).
% 3.42/1.48  tff(c_519, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_516])).
% 3.42/1.48  tff(c_523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_519])).
% 3.42/1.48  tff(c_525, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_450])).
% 3.42/1.48  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.42/1.48  tff(c_169, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_154])).
% 3.42/1.48  tff(c_117, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_106, c_79])).
% 3.42/1.48  tff(c_288, plain, (![A_91, B_92]: (r1_xboole_0(u1_struct_0(A_91), u1_struct_0(B_92)) | ~r1_tsep_1(A_91, B_92) | ~l1_struct_0(B_92) | ~l1_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.42/1.48  tff(c_306, plain, (![B_92]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_92)) | ~r1_tsep_1('#skF_7', B_92) | ~l1_struct_0(B_92) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_288])).
% 3.42/1.48  tff(c_466, plain, (![B_104]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_104)) | ~r1_tsep_1('#skF_7', B_104) | ~l1_struct_0(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_306])).
% 3.42/1.48  tff(c_472, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_125, c_466])).
% 3.42/1.48  tff(c_484, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_169, c_472])).
% 3.42/1.48  tff(c_258, plain, (![B_88, A_89]: (r1_tarski(k2_struct_0(B_88), k2_struct_0(A_89)) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.42/1.48  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.48  tff(c_794, plain, (![B_123, A_124]: (k2_xboole_0(k2_struct_0(B_123), k2_struct_0(A_124))=k2_struct_0(A_124) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(B_123) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_258, c_2])).
% 3.42/1.48  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.48  tff(c_841, plain, (![A_128, B_129, A_130]: (r1_xboole_0(A_128, k2_struct_0(B_129)) | ~r1_xboole_0(A_128, k2_struct_0(A_130)) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(B_129) | ~l1_pre_topc(A_130))), inference(superposition, [status(thm), theory('equality')], [c_794, c_8])).
% 3.42/1.48  tff(c_847, plain, (![B_129]: (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0(B_129)) | ~m1_pre_topc(B_129, '#skF_6') | ~l1_pre_topc(B_129) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_484, c_841])).
% 3.42/1.48  tff(c_872, plain, (![B_131]: (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0(B_131)) | ~m1_pre_topc(B_131, '#skF_6') | ~l1_pre_topc(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_847])).
% 3.42/1.48  tff(c_475, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_121, c_466])).
% 3.42/1.48  tff(c_645, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~r1_tsep_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_475])).
% 3.42/1.48  tff(c_646, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_645])).
% 3.42/1.48  tff(c_205, plain, (![B_86]: (r1_tsep_1('#skF_7', B_86) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_86)) | ~l1_struct_0(B_86) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_190])).
% 3.42/1.48  tff(c_329, plain, (![B_93]: (r1_tsep_1('#skF_7', B_93) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_93)) | ~l1_struct_0(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_205])).
% 3.42/1.48  tff(c_335, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_121, c_329])).
% 3.42/1.48  tff(c_651, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_335])).
% 3.42/1.48  tff(c_652, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_646, c_651])).
% 3.42/1.48  tff(c_877, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_872, c_652])).
% 3.42/1.48  tff(c_888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_54, c_877])).
% 3.42/1.48  tff(c_890, plain, (r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_645])).
% 3.42/1.48  tff(c_48, plain, (![B_55, A_54]: (r1_tsep_1(B_55, A_54) | ~r1_tsep_1(A_54, B_55) | ~l1_struct_0(B_55) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.48  tff(c_892, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_890, c_48])).
% 3.42/1.48  tff(c_895, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_525, c_892])).
% 3.42/1.48  tff(c_897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_895])).
% 3.42/1.48  tff(c_898, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.48  tff(c_899, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.42/1.48  tff(c_961, plain, (![B_143, A_144]: (r1_tsep_1(B_143, A_144) | ~r1_tsep_1(A_144, B_143) | ~l1_struct_0(B_143) | ~l1_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.48  tff(c_963, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_899, c_961])).
% 3.42/1.48  tff(c_968, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_898, c_963])).
% 3.42/1.48  tff(c_979, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_968])).
% 3.42/1.48  tff(c_982, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_979])).
% 3.42/1.48  tff(c_986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_928, c_982])).
% 3.42/1.48  tff(c_987, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_968])).
% 3.42/1.48  tff(c_997, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_987])).
% 3.42/1.48  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_925, c_997])).
% 3.42/1.48  tff(c_1003, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 3.42/1.48  tff(c_1002, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 3.42/1.48  tff(c_1071, plain, (![B_160, A_161]: (r1_tsep_1(B_160, A_161) | ~r1_tsep_1(A_161, B_160) | ~l1_struct_0(B_160) | ~l1_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.42/1.48  tff(c_1073, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1002, c_1071])).
% 3.42/1.48  tff(c_1076, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1003, c_1073])).
% 3.42/1.48  tff(c_1077, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1076])).
% 3.42/1.48  tff(c_1080, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_1077])).
% 3.42/1.48  tff(c_1084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1035, c_1080])).
% 3.42/1.48  tff(c_1085, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1076])).
% 3.42/1.48  tff(c_1089, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_1085])).
% 3.42/1.48  tff(c_1093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1042, c_1089])).
% 3.42/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.48  
% 3.42/1.48  Inference rules
% 3.42/1.48  ----------------------
% 3.42/1.48  #Ref     : 0
% 3.42/1.48  #Sup     : 196
% 3.42/1.48  #Fact    : 0
% 3.42/1.48  #Define  : 0
% 3.42/1.48  #Split   : 23
% 3.42/1.48  #Chain   : 0
% 3.42/1.48  #Close   : 0
% 3.42/1.48  
% 3.42/1.48  Ordering : KBO
% 3.42/1.48  
% 3.42/1.48  Simplification rules
% 3.42/1.48  ----------------------
% 3.42/1.48  #Subsume      : 29
% 3.42/1.48  #Demod        : 151
% 3.42/1.49  #Tautology    : 59
% 3.42/1.49  #SimpNegUnit  : 43
% 3.42/1.49  #BackRed      : 0
% 3.42/1.49  
% 3.42/1.49  #Partial instantiations: 0
% 3.42/1.49  #Strategies tried      : 1
% 3.42/1.49  
% 3.42/1.49  Timing (in seconds)
% 3.42/1.49  ----------------------
% 3.42/1.49  Preprocessing        : 0.33
% 3.42/1.49  Parsing              : 0.17
% 3.42/1.49  CNF conversion       : 0.03
% 3.42/1.49  Main loop            : 0.39
% 3.42/1.49  Inferencing          : 0.13
% 3.42/1.49  Reduction            : 0.12
% 3.42/1.49  Demodulation         : 0.08
% 3.42/1.49  BG Simplification    : 0.02
% 3.42/1.49  Subsumption          : 0.07
% 3.42/1.49  Abstraction          : 0.02
% 3.42/1.49  MUC search           : 0.00
% 3.42/1.49  Cooper               : 0.00
% 3.42/1.49  Total                : 0.77
% 3.42/1.49  Index Insertion      : 0.00
% 3.42/1.49  Index Deletion       : 0.00
% 3.42/1.49  Index Matching       : 0.00
% 3.42/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
