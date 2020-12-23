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
% DateTime   : Thu Dec  3 10:26:34 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 641 expanded)
%              Number of leaves         :   39 ( 215 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 (2267 expanded)
%              Number of equality atoms :   13 (  80 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_197,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_80,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_86,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_74,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1261,plain,(
    ! [B_190,A_191] :
      ( l1_pre_topc(B_190)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1264,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1261])).

tff(c_1276,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1264])).

tff(c_48,plain,(
    ! [A_52] :
      ( l1_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1267,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1261])).

tff(c_1279,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1267])).

tff(c_78,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1163,plain,(
    ! [B_175,A_176] :
      ( l1_pre_topc(B_175)
      | ~ m1_pre_topc(B_175,A_176)
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1175,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1163])).

tff(c_1185,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1175])).

tff(c_1166,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1163])).

tff(c_1178,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1166])).

tff(c_70,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_100,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_111,plain,(
    ! [B_96,A_97] :
      ( l1_pre_topc(B_96)
      | ~ m1_pre_topc(B_96,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_114,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_111])).

tff(c_126,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_114])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_111])).

tff(c_133,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_123])).

tff(c_68,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_101,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_173,plain,(
    ! [B_108,A_109] :
      ( r1_tsep_1(B_108,A_109)
      | ~ r1_tsep_1(A_109,B_108)
      | ~ l1_struct_0(B_108)
      | ~ l1_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_176,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_101,c_173])).

tff(c_177,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_180,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_180])).

tff(c_185,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_201,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_204,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_204])).

tff(c_210,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_111])).

tff(c_129,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_117])).

tff(c_95,plain,(
    ! [A_94] :
      ( u1_struct_0(A_94) = k2_struct_0(A_94)
      | ~ l1_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_48,c_95])).

tff(c_141,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_129,c_99])).

tff(c_137,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_126,c_99])).

tff(c_317,plain,(
    ! [A_121,B_122] :
      ( r1_tsep_1(A_121,B_122)
      | ~ r1_xboole_0(u1_struct_0(A_121),u1_struct_0(B_122))
      | ~ l1_struct_0(B_122)
      | ~ l1_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_335,plain,(
    ! [A_121] :
      ( r1_tsep_1(A_121,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_121),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_317])).

tff(c_384,plain,(
    ! [A_124] :
      ( r1_tsep_1(A_124,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_124),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_335])).

tff(c_387,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_384])).

tff(c_397,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_387])).

tff(c_445,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_448,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_445])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_448])).

tff(c_454,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_72,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    ! [B_34,A_12] :
      ( r1_tarski(k2_struct_0(B_34),k2_struct_0(A_12))
      | ~ m1_pre_topc(B_34,A_12)
      | ~ l1_pre_topc(B_34)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_209,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_186,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_145,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_99])).

tff(c_404,plain,(
    ! [A_125,B_126] :
      ( r1_xboole_0(u1_struct_0(A_125),u1_struct_0(B_126))
      | ~ r1_tsep_1(A_125,B_126)
      | ~ l1_struct_0(B_126)
      | ~ l1_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_419,plain,(
    ! [A_125] :
      ( r1_xboole_0(u1_struct_0(A_125),k2_struct_0('#skF_6'))
      | ~ r1_tsep_1(A_125,'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_404])).

tff(c_682,plain,(
    ! [A_145] :
      ( r1_xboole_0(u1_struct_0(A_145),k2_struct_0('#skF_6'))
      | ~ r1_tsep_1(A_145,'#skF_6')
      | ~ l1_struct_0(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_419])).

tff(c_694,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_682])).

tff(c_706,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_209,c_694])).

tff(c_16,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_221,plain,(
    ! [A_113,C_114,B_115] :
      ( r1_tarski(k2_xboole_0(A_113,C_114),B_115)
      | ~ r1_tarski(C_114,B_115)
      | ~ r1_tarski(A_113,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [B_104,A_105] :
      ( B_104 = A_105
      | ~ r1_tarski(B_104,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_162])).

tff(c_225,plain,(
    ! [B_115,C_114] :
      ( k2_xboole_0(B_115,C_114) = B_115
      | ~ r1_tarski(C_114,B_115)
      | ~ r1_tarski(B_115,B_115) ) ),
    inference(resolution,[status(thm)],[c_221,c_167])).

tff(c_232,plain,(
    ! [B_116,C_117] :
      ( k2_xboole_0(B_116,C_117) = B_116
      | ~ r1_tarski(C_117,B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_225])).

tff(c_829,plain,(
    ! [B_156,A_157,C_158] :
      ( k2_xboole_0(B_156,k2_xboole_0(A_157,C_158)) = B_156
      | ~ r1_tarski(C_158,B_156)
      | ~ r1_tarski(A_157,B_156) ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1004,plain,(
    ! [A_163,A_164,C_165,B_166] :
      ( r1_xboole_0(A_163,k2_xboole_0(A_164,C_165))
      | ~ r1_xboole_0(A_163,B_166)
      | ~ r1_tarski(C_165,B_166)
      | ~ r1_tarski(A_164,B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_10])).

tff(c_1041,plain,(
    ! [A_167,C_168] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),k2_xboole_0(A_167,C_168))
      | ~ r1_tarski(C_168,k2_struct_0('#skF_6'))
      | ~ r1_tarski(A_167,k2_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_706,c_1004])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1063,plain,(
    ! [A_167,C_168] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),A_167)
      | ~ r1_tarski(C_168,k2_struct_0('#skF_6'))
      | ~ r1_tarski(A_167,k2_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1041,c_12])).

tff(c_1066,plain,(
    ! [C_169] : ~ r1_tarski(C_169,k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1063])).

tff(c_1083,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1066])).

tff(c_1106,plain,(
    ! [A_173] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),A_173)
      | ~ r1_tarski(A_173,k2_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1063])).

tff(c_332,plain,(
    ! [B_122] :
      ( r1_tsep_1('#skF_7',B_122)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_122))
      | ~ l1_struct_0(B_122)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_317])).

tff(c_710,plain,(
    ! [B_146] :
      ( r1_tsep_1('#skF_7',B_146)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_146))
      | ~ l1_struct_0(B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_332])).

tff(c_713,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_710])).

tff(c_724,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_713])).

tff(c_738,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_1130,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1106,c_738])).

tff(c_1138,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1130])).

tff(c_1142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_129,c_72,c_1138])).

tff(c_1143,plain,(
    r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_66,plain,(
    ! [B_78,A_77] :
      ( r1_tsep_1(B_78,A_77)
      | ~ r1_tsep_1(A_77,B_78)
      | ~ l1_struct_0(B_78)
      | ~ l1_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1146,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1143,c_66])).

tff(c_1149,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_454,c_1146])).

tff(c_1151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1149])).

tff(c_1153,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1152,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1225,plain,(
    ! [B_187,A_188] :
      ( r1_tsep_1(B_187,A_188)
      | ~ r1_tsep_1(A_188,B_187)
      | ~ l1_struct_0(B_187)
      | ~ l1_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1227,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1152,c_1225])).

tff(c_1230,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1153,c_1227])).

tff(c_1231,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1230])).

tff(c_1234,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1231])).

tff(c_1238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1234])).

tff(c_1239,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1230])).

tff(c_1248,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_1239])).

tff(c_1252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1248])).

tff(c_1253,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1254,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1327,plain,(
    ! [B_202,A_203] :
      ( r1_tsep_1(B_202,A_203)
      | ~ r1_tsep_1(A_203,B_202)
      | ~ l1_struct_0(B_202)
      | ~ l1_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1331,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1254,c_1327])).

tff(c_1335,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_1331])).

tff(c_1336,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1335])).

tff(c_1339,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_1336])).

tff(c_1343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_1339])).

tff(c_1344,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1335])).

tff(c_1348,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1344])).

tff(c_1352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_1348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.60  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.49/1.60  
% 3.49/1.60  %Foreground sorts:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Background operators:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Foreground operators:
% 3.49/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.60  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.49/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.49/1.60  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.49/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.49/1.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.49/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.49/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.49/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.60  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.49/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.49/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.49/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.60  
% 3.49/1.62  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.49/1.62  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.49/1.62  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.49/1.62  tff(f_159, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.49/1.62  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.49/1.62  tff(f_129, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.49/1.62  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.49/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.49/1.62  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.49/1.62  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.49/1.62  tff(f_47, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.49/1.62  tff(c_86, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_74, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_1261, plain, (![B_190, A_191]: (l1_pre_topc(B_190) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.49/1.62  tff(c_1264, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1261])).
% 3.49/1.62  tff(c_1276, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1264])).
% 3.49/1.62  tff(c_48, plain, (![A_52]: (l1_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.49/1.62  tff(c_82, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_1267, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_82, c_1261])).
% 3.49/1.62  tff(c_1279, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1267])).
% 3.49/1.62  tff(c_78, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_1163, plain, (![B_175, A_176]: (l1_pre_topc(B_175) | ~m1_pre_topc(B_175, A_176) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.49/1.62  tff(c_1175, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1163])).
% 3.49/1.62  tff(c_1185, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1175])).
% 3.49/1.62  tff(c_1166, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1163])).
% 3.49/1.62  tff(c_1178, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1166])).
% 3.49/1.62  tff(c_70, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_100, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 3.49/1.62  tff(c_111, plain, (![B_96, A_97]: (l1_pre_topc(B_96) | ~m1_pre_topc(B_96, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.49/1.62  tff(c_114, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_74, c_111])).
% 3.49/1.62  tff(c_126, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_114])).
% 3.49/1.62  tff(c_123, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_111])).
% 3.49/1.62  tff(c_133, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_123])).
% 3.49/1.62  tff(c_68, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_101, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_68])).
% 3.49/1.62  tff(c_173, plain, (![B_108, A_109]: (r1_tsep_1(B_108, A_109) | ~r1_tsep_1(A_109, B_108) | ~l1_struct_0(B_108) | ~l1_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.49/1.62  tff(c_176, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_101, c_173])).
% 3.49/1.62  tff(c_177, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_176])).
% 3.49/1.62  tff(c_180, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_177])).
% 3.49/1.62  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_180])).
% 3.49/1.62  tff(c_185, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_176])).
% 3.49/1.62  tff(c_201, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_185])).
% 3.49/1.62  tff(c_204, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_48, c_201])).
% 3.49/1.62  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_204])).
% 3.49/1.62  tff(c_210, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_185])).
% 3.49/1.62  tff(c_117, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_82, c_111])).
% 3.49/1.62  tff(c_129, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_117])).
% 3.49/1.62  tff(c_95, plain, (![A_94]: (u1_struct_0(A_94)=k2_struct_0(A_94) | ~l1_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.49/1.62  tff(c_99, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_48, c_95])).
% 3.49/1.62  tff(c_141, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_129, c_99])).
% 3.49/1.62  tff(c_137, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_126, c_99])).
% 3.49/1.62  tff(c_317, plain, (![A_121, B_122]: (r1_tsep_1(A_121, B_122) | ~r1_xboole_0(u1_struct_0(A_121), u1_struct_0(B_122)) | ~l1_struct_0(B_122) | ~l1_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.49/1.62  tff(c_335, plain, (![A_121]: (r1_tsep_1(A_121, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_121), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_121))), inference(superposition, [status(thm), theory('equality')], [c_137, c_317])).
% 3.49/1.62  tff(c_384, plain, (![A_124]: (r1_tsep_1(A_124, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_124), k2_struct_0('#skF_7')) | ~l1_struct_0(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_335])).
% 3.49/1.62  tff(c_387, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_141, c_384])).
% 3.49/1.62  tff(c_397, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_100, c_387])).
% 3.49/1.62  tff(c_445, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_397])).
% 3.49/1.62  tff(c_448, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_445])).
% 3.49/1.62  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_448])).
% 3.49/1.62  tff(c_454, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_397])).
% 3.49/1.62  tff(c_72, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.49/1.62  tff(c_38, plain, (![B_34, A_12]: (r1_tarski(k2_struct_0(B_34), k2_struct_0(A_12)) | ~m1_pre_topc(B_34, A_12) | ~l1_pre_topc(B_34) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.49/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.62  tff(c_209, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_185])).
% 3.49/1.62  tff(c_186, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_176])).
% 3.49/1.62  tff(c_145, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_133, c_99])).
% 3.49/1.62  tff(c_404, plain, (![A_125, B_126]: (r1_xboole_0(u1_struct_0(A_125), u1_struct_0(B_126)) | ~r1_tsep_1(A_125, B_126) | ~l1_struct_0(B_126) | ~l1_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.49/1.62  tff(c_419, plain, (![A_125]: (r1_xboole_0(u1_struct_0(A_125), k2_struct_0('#skF_6')) | ~r1_tsep_1(A_125, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(A_125))), inference(superposition, [status(thm), theory('equality')], [c_145, c_404])).
% 3.49/1.62  tff(c_682, plain, (![A_145]: (r1_xboole_0(u1_struct_0(A_145), k2_struct_0('#skF_6')) | ~r1_tsep_1(A_145, '#skF_6') | ~l1_struct_0(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_419])).
% 3.49/1.62  tff(c_694, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_137, c_682])).
% 3.49/1.62  tff(c_706, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_209, c_694])).
% 3.49/1.62  tff(c_16, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.62  tff(c_221, plain, (![A_113, C_114, B_115]: (r1_tarski(k2_xboole_0(A_113, C_114), B_115) | ~r1_tarski(C_114, B_115) | ~r1_tarski(A_113, B_115))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.62  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.49/1.62  tff(c_162, plain, (![B_104, A_105]: (B_104=A_105 | ~r1_tarski(B_104, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.62  tff(c_167, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(k2_xboole_0(A_6, B_7), A_6))), inference(resolution, [status(thm)], [c_14, c_162])).
% 3.49/1.62  tff(c_225, plain, (![B_115, C_114]: (k2_xboole_0(B_115, C_114)=B_115 | ~r1_tarski(C_114, B_115) | ~r1_tarski(B_115, B_115))), inference(resolution, [status(thm)], [c_221, c_167])).
% 3.49/1.62  tff(c_232, plain, (![B_116, C_117]: (k2_xboole_0(B_116, C_117)=B_116 | ~r1_tarski(C_117, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_225])).
% 3.49/1.62  tff(c_829, plain, (![B_156, A_157, C_158]: (k2_xboole_0(B_156, k2_xboole_0(A_157, C_158))=B_156 | ~r1_tarski(C_158, B_156) | ~r1_tarski(A_157, B_156))), inference(resolution, [status(thm)], [c_16, c_232])).
% 3.49/1.62  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.62  tff(c_1004, plain, (![A_163, A_164, C_165, B_166]: (r1_xboole_0(A_163, k2_xboole_0(A_164, C_165)) | ~r1_xboole_0(A_163, B_166) | ~r1_tarski(C_165, B_166) | ~r1_tarski(A_164, B_166))), inference(superposition, [status(thm), theory('equality')], [c_829, c_10])).
% 3.49/1.62  tff(c_1041, plain, (![A_167, C_168]: (r1_xboole_0(k2_struct_0('#skF_7'), k2_xboole_0(A_167, C_168)) | ~r1_tarski(C_168, k2_struct_0('#skF_6')) | ~r1_tarski(A_167, k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_706, c_1004])).
% 3.49/1.62  tff(c_12, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.62  tff(c_1063, plain, (![A_167, C_168]: (r1_xboole_0(k2_struct_0('#skF_7'), A_167) | ~r1_tarski(C_168, k2_struct_0('#skF_6')) | ~r1_tarski(A_167, k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1041, c_12])).
% 3.49/1.62  tff(c_1066, plain, (![C_169]: (~r1_tarski(C_169, k2_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_1063])).
% 3.49/1.62  tff(c_1083, plain, $false, inference(resolution, [status(thm)], [c_6, c_1066])).
% 3.49/1.62  tff(c_1106, plain, (![A_173]: (r1_xboole_0(k2_struct_0('#skF_7'), A_173) | ~r1_tarski(A_173, k2_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1063])).
% 3.49/1.62  tff(c_332, plain, (![B_122]: (r1_tsep_1('#skF_7', B_122) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_122)) | ~l1_struct_0(B_122) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_317])).
% 3.49/1.62  tff(c_710, plain, (![B_146]: (r1_tsep_1('#skF_7', B_146) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_146)) | ~l1_struct_0(B_146))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_332])).
% 3.49/1.62  tff(c_713, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_141, c_710])).
% 3.49/1.62  tff(c_724, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_713])).
% 3.49/1.62  tff(c_738, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_724])).
% 3.49/1.62  tff(c_1130, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1106, c_738])).
% 3.49/1.62  tff(c_1138, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1130])).
% 3.49/1.62  tff(c_1142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_129, c_72, c_1138])).
% 3.49/1.62  tff(c_1143, plain, (r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_724])).
% 3.49/1.62  tff(c_66, plain, (![B_78, A_77]: (r1_tsep_1(B_78, A_77) | ~r1_tsep_1(A_77, B_78) | ~l1_struct_0(B_78) | ~l1_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.49/1.62  tff(c_1146, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1143, c_66])).
% 3.49/1.62  tff(c_1149, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_454, c_1146])).
% 3.49/1.62  tff(c_1151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1149])).
% 3.49/1.62  tff(c_1153, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 3.49/1.62  tff(c_1152, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 3.49/1.62  tff(c_1225, plain, (![B_187, A_188]: (r1_tsep_1(B_187, A_188) | ~r1_tsep_1(A_188, B_187) | ~l1_struct_0(B_187) | ~l1_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.49/1.62  tff(c_1227, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1152, c_1225])).
% 3.49/1.62  tff(c_1230, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1153, c_1227])).
% 3.49/1.62  tff(c_1231, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1230])).
% 3.49/1.62  tff(c_1234, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1231])).
% 3.49/1.62  tff(c_1238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1234])).
% 3.49/1.62  tff(c_1239, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1230])).
% 3.49/1.62  tff(c_1248, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_1239])).
% 3.49/1.62  tff(c_1252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1248])).
% 3.49/1.62  tff(c_1253, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 3.49/1.62  tff(c_1254, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 3.49/1.62  tff(c_1327, plain, (![B_202, A_203]: (r1_tsep_1(B_202, A_203) | ~r1_tsep_1(A_203, B_202) | ~l1_struct_0(B_202) | ~l1_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.49/1.62  tff(c_1331, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1254, c_1327])).
% 3.49/1.62  tff(c_1335, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1253, c_1331])).
% 3.49/1.62  tff(c_1336, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1335])).
% 3.49/1.62  tff(c_1339, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48, c_1336])).
% 3.49/1.62  tff(c_1343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1279, c_1339])).
% 3.49/1.62  tff(c_1344, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1335])).
% 3.49/1.62  tff(c_1348, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1344])).
% 3.49/1.62  tff(c_1352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1276, c_1348])).
% 3.49/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.62  
% 3.49/1.62  Inference rules
% 3.49/1.62  ----------------------
% 3.49/1.62  #Ref     : 0
% 3.49/1.62  #Sup     : 259
% 3.49/1.62  #Fact    : 0
% 3.49/1.62  #Define  : 0
% 3.49/1.62  #Split   : 23
% 3.49/1.62  #Chain   : 0
% 3.49/1.62  #Close   : 0
% 3.49/1.62  
% 3.49/1.62  Ordering : KBO
% 3.49/1.62  
% 3.49/1.62  Simplification rules
% 3.49/1.62  ----------------------
% 3.49/1.62  #Subsume      : 41
% 3.49/1.62  #Demod        : 159
% 3.49/1.62  #Tautology    : 91
% 3.49/1.62  #SimpNegUnit  : 42
% 3.49/1.62  #BackRed      : 0
% 3.49/1.62  
% 3.49/1.62  #Partial instantiations: 0
% 3.49/1.62  #Strategies tried      : 1
% 3.49/1.62  
% 3.49/1.62  Timing (in seconds)
% 3.49/1.62  ----------------------
% 3.49/1.62  Preprocessing        : 0.38
% 3.49/1.62  Parsing              : 0.19
% 3.49/1.62  CNF conversion       : 0.03
% 3.49/1.62  Main loop            : 0.47
% 3.49/1.62  Inferencing          : 0.16
% 3.49/1.62  Reduction            : 0.15
% 3.49/1.62  Demodulation         : 0.10
% 3.49/1.62  BG Simplification    : 0.03
% 3.49/1.62  Subsumption          : 0.10
% 3.49/1.62  Abstraction          : 0.03
% 3.49/1.62  MUC search           : 0.00
% 3.49/1.62  Cooper               : 0.00
% 3.49/1.62  Total                : 0.90
% 3.49/1.62  Index Insertion      : 0.00
% 3.49/1.62  Index Deletion       : 0.00
% 3.49/1.62  Index Matching       : 0.00
% 3.49/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
