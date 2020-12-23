%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:38 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 341 expanded)
%              Number of leaves         :   34 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 (1229 expanded)
%              Number of equality atoms :    8 (  26 expanded)
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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_84,axiom,(
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

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_889,plain,(
    ! [B_130,A_131] :
      ( l1_pre_topc(B_130)
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_901,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_889])).

tff(c_911,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_901])).

tff(c_40,plain,(
    ! [A_48] :
      ( l1_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_892,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_889])).

tff(c_904,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_892])).

tff(c_756,plain,(
    ! [B_120,A_121] :
      ( l1_pre_topc(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_759,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_756])).

tff(c_771,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_759])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_762,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_756])).

tff(c_774,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_762])).

tff(c_92,plain,(
    ! [B_72,A_73] :
      ( l1_pre_topc(B_72)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_114,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_104])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_110,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_98])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    ! [B_30,A_8] :
      ( r1_tarski(k2_struct_0(B_30),k2_struct_0(A_8))
      | ~ m1_pre_topc(B_30,A_8)
      | ~ l1_pre_topc(B_30)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_107,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_95])).

tff(c_52,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_76,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_148,plain,(
    ! [B_76,A_77] :
      ( r1_tsep_1(B_76,A_77)
      | ~ r1_tsep_1(A_77,B_76)
      | ~ l1_struct_0(B_76)
      | ~ l1_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_151,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_148])).

tff(c_152,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_155])).

tff(c_160,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_170])).

tff(c_176,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_78,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_118,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_107,c_82])).

tff(c_161,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_126,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_82])).

tff(c_191,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(u1_struct_0(A_80),u1_struct_0(B_81))
      | ~ r1_tsep_1(A_80,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_194,plain,(
    ! [B_81] :
      ( r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_81))
      | ~ r1_tsep_1('#skF_6',B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_191])).

tff(c_224,plain,(
    ! [B_82] :
      ( r1_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(B_82))
      | ~ r1_tsep_1('#skF_6',B_82)
      | ~ l1_struct_0(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_194])).

tff(c_233,plain,
    ( r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'))
    | ~ r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_224])).

tff(c_240,plain,(
    r1_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_76,c_233])).

tff(c_341,plain,(
    ! [A_87,C_88,B_89,D_90] :
      ( r1_xboole_0(A_87,C_88)
      | ~ r1_xboole_0(B_89,D_90)
      | ~ r1_tarski(C_88,D_90)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_681,plain,(
    ! [A_113,C_114] :
      ( r1_xboole_0(A_113,C_114)
      | ~ r1_tarski(C_114,k2_struct_0('#skF_7'))
      | ~ r1_tarski(A_113,k2_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_240,c_341])).

tff(c_692,plain,(
    ! [A_115] :
      ( r1_xboole_0(A_115,k2_struct_0('#skF_7'))
      | ~ r1_tarski(A_115,k2_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_681])).

tff(c_50,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_77,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_122,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_82])).

tff(c_257,plain,(
    ! [A_83,B_84] :
      ( r1_tsep_1(A_83,B_84)
      | ~ r1_xboole_0(u1_struct_0(A_83),u1_struct_0(B_84))
      | ~ l1_struct_0(B_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_278,plain,(
    ! [A_83] :
      ( r1_tsep_1(A_83,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_83),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_257])).

tff(c_533,plain,(
    ! [A_102] :
      ( r1_tsep_1(A_102,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_102),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_278])).

tff(c_539,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_533])).

tff(c_548,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_539])).

tff(c_555,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_558,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_555])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_558])).

tff(c_563,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_707,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_692,c_563])).

tff(c_735,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_707])).

tff(c_739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_110,c_54,c_735])).

tff(c_740,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_741,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_812,plain,(
    ! [B_124,A_125] :
      ( r1_tsep_1(B_124,A_125)
      | ~ r1_tsep_1(A_125,B_124)
      | ~ l1_struct_0(B_124)
      | ~ l1_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_814,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_741,c_812])).

tff(c_819,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_814])).

tff(c_821,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_819])).

tff(c_824,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_821])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_824])).

tff(c_829,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_867,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_829])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_867])).

tff(c_873,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_872,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_945,plain,(
    ! [B_134,A_135] :
      ( r1_tsep_1(B_134,A_135)
      | ~ r1_tsep_1(A_135,B_134)
      | ~ l1_struct_0(B_134)
      | ~ l1_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_947,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_872,c_945])).

tff(c_950,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_947])).

tff(c_951,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_979,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_951])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_904,c_979])).

tff(c_984,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_988,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_984])).

tff(c_992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.35  % Computer   : n018.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 15:05:12 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.42  
% 3.13/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.42  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.13/1.42  
% 3.13/1.42  %Foreground sorts:
% 3.13/1.42  
% 3.13/1.42  
% 3.13/1.42  %Background operators:
% 3.13/1.42  
% 3.13/1.42  
% 3.13/1.42  %Foreground operators:
% 3.13/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.13/1.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.13/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.42  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.13/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.42  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.42  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.13/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.42  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.13/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.42  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.13/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.13/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.13/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.42  
% 3.13/1.44  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 3.13/1.44  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.13/1.44  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.13/1.44  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.13/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.44  tff(f_92, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.13/1.44  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.13/1.44  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.13/1.44  tff(f_39, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 3.13/1.44  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_889, plain, (![B_130, A_131]: (l1_pre_topc(B_130) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.13/1.44  tff(c_901, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_889])).
% 3.13/1.44  tff(c_911, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_901])).
% 3.13/1.44  tff(c_40, plain, (![A_48]: (l1_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.44  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_892, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_889])).
% 3.13/1.44  tff(c_904, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_892])).
% 3.13/1.44  tff(c_756, plain, (![B_120, A_121]: (l1_pre_topc(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.13/1.44  tff(c_759, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_756])).
% 3.13/1.44  tff(c_771, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_759])).
% 3.13/1.44  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_762, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_756])).
% 3.13/1.44  tff(c_774, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_762])).
% 3.13/1.44  tff(c_92, plain, (![B_72, A_73]: (l1_pre_topc(B_72) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.13/1.44  tff(c_104, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_92])).
% 3.13/1.44  tff(c_114, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_104])).
% 3.13/1.44  tff(c_98, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_92])).
% 3.13/1.44  tff(c_110, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_98])).
% 3.13/1.44  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_30, plain, (![B_30, A_8]: (r1_tarski(k2_struct_0(B_30), k2_struct_0(A_8)) | ~m1_pre_topc(B_30, A_8) | ~l1_pre_topc(B_30) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.13/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.44  tff(c_95, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_92])).
% 3.13/1.44  tff(c_107, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_95])).
% 3.13/1.44  tff(c_52, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_76, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 3.13/1.44  tff(c_148, plain, (![B_76, A_77]: (r1_tsep_1(B_76, A_77) | ~r1_tsep_1(A_77, B_76) | ~l1_struct_0(B_76) | ~l1_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.13/1.44  tff(c_151, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_76, c_148])).
% 3.13/1.44  tff(c_152, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_151])).
% 3.13/1.44  tff(c_155, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_152])).
% 3.13/1.44  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_155])).
% 3.13/1.44  tff(c_160, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_151])).
% 3.13/1.44  tff(c_167, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_160])).
% 3.13/1.44  tff(c_170, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_167])).
% 3.13/1.44  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_170])).
% 3.13/1.44  tff(c_176, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_160])).
% 3.13/1.44  tff(c_78, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.44  tff(c_82, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_40, c_78])).
% 3.13/1.44  tff(c_118, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_107, c_82])).
% 3.13/1.44  tff(c_161, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_151])).
% 3.13/1.44  tff(c_126, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_114, c_82])).
% 3.13/1.44  tff(c_191, plain, (![A_80, B_81]: (r1_xboole_0(u1_struct_0(A_80), u1_struct_0(B_81)) | ~r1_tsep_1(A_80, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.13/1.44  tff(c_194, plain, (![B_81]: (r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_81)) | ~r1_tsep_1('#skF_6', B_81) | ~l1_struct_0(B_81) | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_191])).
% 3.13/1.44  tff(c_224, plain, (![B_82]: (r1_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(B_82)) | ~r1_tsep_1('#skF_6', B_82) | ~l1_struct_0(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_194])).
% 3.13/1.44  tff(c_233, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7')) | ~r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_118, c_224])).
% 3.13/1.44  tff(c_240, plain, (r1_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_76, c_233])).
% 3.13/1.44  tff(c_341, plain, (![A_87, C_88, B_89, D_90]: (r1_xboole_0(A_87, C_88) | ~r1_xboole_0(B_89, D_90) | ~r1_tarski(C_88, D_90) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.44  tff(c_681, plain, (![A_113, C_114]: (r1_xboole_0(A_113, C_114) | ~r1_tarski(C_114, k2_struct_0('#skF_7')) | ~r1_tarski(A_113, k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_240, c_341])).
% 3.13/1.44  tff(c_692, plain, (![A_115]: (r1_xboole_0(A_115, k2_struct_0('#skF_7')) | ~r1_tarski(A_115, k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_681])).
% 3.13/1.44  tff(c_50, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.44  tff(c_77, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 3.13/1.44  tff(c_122, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_110, c_82])).
% 3.13/1.44  tff(c_257, plain, (![A_83, B_84]: (r1_tsep_1(A_83, B_84) | ~r1_xboole_0(u1_struct_0(A_83), u1_struct_0(B_84)) | ~l1_struct_0(B_84) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.13/1.44  tff(c_278, plain, (![A_83]: (r1_tsep_1(A_83, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_83), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_83))), inference(superposition, [status(thm), theory('equality')], [c_118, c_257])).
% 3.13/1.44  tff(c_533, plain, (![A_102]: (r1_tsep_1(A_102, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_102), k2_struct_0('#skF_7')) | ~l1_struct_0(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_278])).
% 3.13/1.44  tff(c_539, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_122, c_533])).
% 3.13/1.44  tff(c_548, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_77, c_539])).
% 3.13/1.44  tff(c_555, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_548])).
% 3.13/1.44  tff(c_558, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_555])).
% 3.13/1.44  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_558])).
% 3.13/1.44  tff(c_563, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_548])).
% 3.13/1.44  tff(c_707, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_692, c_563])).
% 3.13/1.44  tff(c_735, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_30, c_707])).
% 3.13/1.44  tff(c_739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_110, c_54, c_735])).
% 3.13/1.44  tff(c_740, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 3.13/1.44  tff(c_741, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.13/1.44  tff(c_812, plain, (![B_124, A_125]: (r1_tsep_1(B_124, A_125) | ~r1_tsep_1(A_125, B_124) | ~l1_struct_0(B_124) | ~l1_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.13/1.44  tff(c_814, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_741, c_812])).
% 3.13/1.44  tff(c_819, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_740, c_814])).
% 3.13/1.44  tff(c_821, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_819])).
% 3.13/1.44  tff(c_824, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_821])).
% 3.13/1.44  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_774, c_824])).
% 3.13/1.44  tff(c_829, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_819])).
% 3.13/1.44  tff(c_867, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_829])).
% 3.13/1.44  tff(c_871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_771, c_867])).
% 3.13/1.44  tff(c_873, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 3.13/1.44  tff(c_872, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 3.13/1.44  tff(c_945, plain, (![B_134, A_135]: (r1_tsep_1(B_134, A_135) | ~r1_tsep_1(A_135, B_134) | ~l1_struct_0(B_134) | ~l1_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.13/1.44  tff(c_947, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_872, c_945])).
% 3.13/1.44  tff(c_950, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_873, c_947])).
% 3.13/1.44  tff(c_951, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_950])).
% 3.13/1.44  tff(c_979, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_951])).
% 3.13/1.44  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_904, c_979])).
% 3.13/1.44  tff(c_984, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_950])).
% 3.13/1.44  tff(c_988, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_984])).
% 3.13/1.44  tff(c_992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_911, c_988])).
% 3.13/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.44  
% 3.13/1.44  Inference rules
% 3.13/1.44  ----------------------
% 3.13/1.44  #Ref     : 0
% 3.13/1.44  #Sup     : 189
% 3.13/1.44  #Fact    : 0
% 3.13/1.44  #Define  : 0
% 3.13/1.44  #Split   : 21
% 3.13/1.44  #Chain   : 0
% 3.13/1.44  #Close   : 0
% 3.13/1.44  
% 3.13/1.44  Ordering : KBO
% 3.13/1.44  
% 3.13/1.44  Simplification rules
% 3.13/1.44  ----------------------
% 3.13/1.44  #Subsume      : 15
% 3.13/1.44  #Demod        : 125
% 3.13/1.44  #Tautology    : 51
% 3.13/1.44  #SimpNegUnit  : 26
% 3.13/1.44  #BackRed      : 0
% 3.13/1.44  
% 3.13/1.44  #Partial instantiations: 0
% 3.13/1.44  #Strategies tried      : 1
% 3.13/1.44  
% 3.13/1.44  Timing (in seconds)
% 3.13/1.44  ----------------------
% 3.13/1.45  Preprocessing        : 0.32
% 3.13/1.45  Parsing              : 0.16
% 3.13/1.45  CNF conversion       : 0.03
% 3.13/1.45  Main loop            : 0.37
% 3.13/1.45  Inferencing          : 0.12
% 3.13/1.45  Reduction            : 0.13
% 3.13/1.45  Demodulation         : 0.08
% 3.13/1.45  BG Simplification    : 0.02
% 3.13/1.45  Subsumption          : 0.07
% 3.13/1.45  Abstraction          : 0.02
% 3.13/1.45  MUC search           : 0.00
% 3.13/1.45  Cooper               : 0.00
% 3.13/1.45  Total                : 0.73
% 3.13/1.45  Index Insertion      : 0.00
% 3.13/1.45  Index Deletion       : 0.00
% 3.13/1.45  Index Matching       : 0.00
% 3.13/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
