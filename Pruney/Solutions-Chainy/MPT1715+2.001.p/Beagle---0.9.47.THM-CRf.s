%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:37 EST 2020

% Result     : Theorem 24.77s
% Output     : CNFRefutation 24.96s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 948 expanded)
%              Number of leaves         :   41 ( 325 expanded)
%              Depth                    :   20
%              Number of atoms          :  464 (4023 expanded)
%              Number of equality atoms :   21 ( 155 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_233,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_195,axiom,(
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

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_181,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_78,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_35610,plain,(
    ! [B_1083,A_1084] :
      ( l1_pre_topc(B_1083)
      | ~ m1_pre_topc(B_1083,A_1084)
      | ~ l1_pre_topc(A_1084) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35613,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_35610])).

tff(c_35625,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_35613])).

tff(c_46,plain,(
    ! [A_50] :
      ( l1_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_35616,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_35610])).

tff(c_35628,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_35616])).

tff(c_82,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_35467,plain,(
    ! [B_1064,A_1065] :
      ( l1_pre_topc(B_1064)
      | ~ m1_pre_topc(B_1064,A_1065)
      | ~ l1_pre_topc(A_1065) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35479,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_35467])).

tff(c_35489,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_35479])).

tff(c_35470,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_35467])).

tff(c_35482,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_35470])).

tff(c_72,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_98,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_114,plain,(
    ! [B_106,A_107] :
      ( l1_pre_topc(B_106)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_114])).

tff(c_129,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_117])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_114])).

tff(c_136,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_126])).

tff(c_74,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_104,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_199,plain,(
    ! [B_118,A_119] :
      ( r1_tsep_1(B_118,A_119)
      | ~ r1_tsep_1(A_119,B_118)
      | ~ l1_struct_0(B_118)
      | ~ l1_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_202,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_199])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_206])).

tff(c_211,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_218,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_221,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_221])).

tff(c_227,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_114])).

tff(c_132,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_120])).

tff(c_99,plain,(
    ! [A_104] :
      ( u1_struct_0(A_104) = k2_struct_0(A_104)
      | ~ l1_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_148,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_103])).

tff(c_140,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_129,c_103])).

tff(c_280,plain,(
    ! [A_125,B_126] :
      ( r1_tsep_1(A_125,B_126)
      | ~ r1_xboole_0(u1_struct_0(A_125),u1_struct_0(B_126))
      | ~ l1_struct_0(B_126)
      | ~ l1_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_301,plain,(
    ! [A_125] :
      ( r1_tsep_1(A_125,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_125),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_280])).

tff(c_669,plain,(
    ! [A_153] :
      ( r1_tsep_1(A_153,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_153),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_301])).

tff(c_672,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_669])).

tff(c_682,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_672])).

tff(c_691,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_694,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_691])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_694])).

tff(c_700,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_92,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_398,plain,(
    ! [B_132,C_133,A_134] :
      ( m1_pre_topc(B_132,C_133)
      | ~ r1_tarski(u1_struct_0(B_132),u1_struct_0(C_133))
      | ~ m1_pre_topc(C_133,A_134)
      | ~ m1_pre_topc(B_132,A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_442,plain,(
    ! [B_136,A_137] :
      ( m1_pre_topc(B_136,B_136)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_6,c_398])).

tff(c_450,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_442])).

tff(c_462,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_450])).

tff(c_76,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_58,plain,(
    ! [A_72,B_73,C_74] :
      ( m1_pre_topc(k1_tsep_1(A_72,B_73,C_74),A_72)
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_212,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_226,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_144,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_103])).

tff(c_247,plain,(
    ! [A_123,B_124] :
      ( r1_xboole_0(u1_struct_0(A_123),u1_struct_0(B_124))
      | ~ r1_tsep_1(A_123,B_124)
      | ~ l1_struct_0(B_124)
      | ~ l1_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_262,plain,(
    ! [B_124] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_124))
      | ~ r1_tsep_1('#skF_7',B_124)
      | ~ l1_struct_0(B_124)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_247])).

tff(c_355,plain,(
    ! [B_130] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_130))
      | ~ r1_tsep_1('#skF_7',B_130)
      | ~ l1_struct_0(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_262])).

tff(c_361,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_355])).

tff(c_369,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_226,c_361])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_66,plain,(
    ! [B_81,A_77,C_83] :
      ( m1_pre_topc(B_81,k1_tsep_1(A_77,B_81,C_83))
      | ~ m1_pre_topc(C_83,A_77)
      | v2_struct_0(C_83)
      | ~ m1_pre_topc(B_81,A_77)
      | v2_struct_0(B_81)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_733,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_pre_topc(k1_tsep_1(A_155,B_156,C_157),A_155)
      | ~ m1_pre_topc(C_157,A_155)
      | v2_struct_0(C_157)
      | ~ m1_pre_topc(B_156,A_155)
      | v2_struct_0(B_156)
      | ~ l1_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_68,plain,(
    ! [B_88,C_90,A_84] :
      ( r1_tarski(u1_struct_0(B_88),u1_struct_0(C_90))
      | ~ m1_pre_topc(B_88,C_90)
      | ~ m1_pre_topc(C_90,A_84)
      | ~ m1_pre_topc(B_88,A_84)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2125,plain,(
    ! [B_354,A_355,B_356,C_357] :
      ( r1_tarski(u1_struct_0(B_354),u1_struct_0(k1_tsep_1(A_355,B_356,C_357)))
      | ~ m1_pre_topc(B_354,k1_tsep_1(A_355,B_356,C_357))
      | ~ m1_pre_topc(B_354,A_355)
      | ~ v2_pre_topc(A_355)
      | ~ m1_pre_topc(C_357,A_355)
      | v2_struct_0(C_357)
      | ~ m1_pre_topc(B_356,A_355)
      | v2_struct_0(B_356)
      | ~ l1_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(resolution,[status(thm)],[c_733,c_68])).

tff(c_34794,plain,(
    ! [A_1047,B_1048,C_1049] :
      ( r1_tarski(k2_struct_0('#skF_6'),u1_struct_0(k1_tsep_1(A_1047,B_1048,C_1049)))
      | ~ m1_pre_topc('#skF_6',k1_tsep_1(A_1047,B_1048,C_1049))
      | ~ m1_pre_topc('#skF_6',A_1047)
      | ~ v2_pre_topc(A_1047)
      | ~ m1_pre_topc(C_1049,A_1047)
      | v2_struct_0(C_1049)
      | ~ m1_pre_topc(B_1048,A_1047)
      | v2_struct_0(B_1048)
      | ~ l1_pre_topc(A_1047)
      | v2_struct_0(A_1047) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2125])).

tff(c_60,plain,(
    ! [A_72,B_73,C_74] :
      ( v1_pre_topc(k1_tsep_1(A_72,B_73,C_74))
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2092,plain,(
    ! [A_346,B_347,C_348] :
      ( u1_struct_0(k1_tsep_1(A_346,B_347,C_348)) = k2_xboole_0(u1_struct_0(B_347),u1_struct_0(C_348))
      | ~ m1_pre_topc(k1_tsep_1(A_346,B_347,C_348),A_346)
      | ~ v1_pre_topc(k1_tsep_1(A_346,B_347,C_348))
      | v2_struct_0(k1_tsep_1(A_346,B_347,C_348))
      | ~ m1_pre_topc(C_348,A_346)
      | v2_struct_0(C_348)
      | ~ m1_pre_topc(B_347,A_346)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2393,plain,(
    ! [A_380,B_381,C_382] :
      ( u1_struct_0(k1_tsep_1(A_380,B_381,C_382)) = k2_xboole_0(u1_struct_0(B_381),u1_struct_0(C_382))
      | ~ v1_pre_topc(k1_tsep_1(A_380,B_381,C_382))
      | v2_struct_0(k1_tsep_1(A_380,B_381,C_382))
      | ~ m1_pre_topc(C_382,A_380)
      | v2_struct_0(C_382)
      | ~ m1_pre_topc(B_381,A_380)
      | v2_struct_0(B_381)
      | ~ l1_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_58,c_2092])).

tff(c_62,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ v2_struct_0(k1_tsep_1(A_72,B_73,C_74))
      | ~ m1_pre_topc(C_74,A_72)
      | v2_struct_0(C_74)
      | ~ m1_pre_topc(B_73,A_72)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2710,plain,(
    ! [A_384,B_385,C_386] :
      ( u1_struct_0(k1_tsep_1(A_384,B_385,C_386)) = k2_xboole_0(u1_struct_0(B_385),u1_struct_0(C_386))
      | ~ v1_pre_topc(k1_tsep_1(A_384,B_385,C_386))
      | ~ m1_pre_topc(C_386,A_384)
      | v2_struct_0(C_386)
      | ~ m1_pre_topc(B_385,A_384)
      | v2_struct_0(B_385)
      | ~ l1_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_2393,c_62])).

tff(c_3006,plain,(
    ! [A_389,B_390,C_391] :
      ( u1_struct_0(k1_tsep_1(A_389,B_390,C_391)) = k2_xboole_0(u1_struct_0(B_390),u1_struct_0(C_391))
      | ~ m1_pre_topc(C_391,A_389)
      | v2_struct_0(C_391)
      | ~ m1_pre_topc(B_390,A_389)
      | v2_struct_0(B_390)
      | ~ l1_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(resolution,[status(thm)],[c_60,c_2710])).

tff(c_3302,plain,(
    ! [A_389,C_391] :
      ( u1_struct_0(k1_tsep_1(A_389,'#skF_6',C_391)) = k2_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(C_391))
      | ~ m1_pre_topc(C_391,A_389)
      | v2_struct_0(C_391)
      | ~ m1_pre_topc('#skF_6',A_389)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_3006])).

tff(c_6266,plain,(
    ! [A_421,C_422] :
      ( u1_struct_0(k1_tsep_1(A_421,'#skF_6',C_422)) = k2_xboole_0(k2_struct_0('#skF_6'),u1_struct_0(C_422))
      | ~ m1_pre_topc(C_422,A_421)
      | v2_struct_0(C_422)
      | ~ m1_pre_topc('#skF_6',A_421)
      | ~ l1_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3302])).

tff(c_6596,plain,(
    ! [A_421] :
      ( u1_struct_0(k1_tsep_1(A_421,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_421)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_6',A_421)
      | ~ l1_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_6266])).

tff(c_6624,plain,(
    ! [A_421] :
      ( u1_struct_0(k1_tsep_1(A_421,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_421)
      | ~ m1_pre_topc('#skF_6',A_421)
      | ~ l1_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6596])).

tff(c_6629,plain,(
    ! [A_424] :
      ( u1_struct_0(k1_tsep_1(A_424,'#skF_6','#skF_5')) = k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_424)
      | ~ m1_pre_topc('#skF_6',A_424)
      | ~ l1_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6596])).

tff(c_172,plain,(
    ! [B_116,A_117] :
      ( v2_pre_topc(B_116)
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_184,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_172])).

tff(c_196,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_184])).

tff(c_530,plain,(
    ! [B_88] :
      ( r1_tarski(u1_struct_0(B_88),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_88,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_462,c_68])).

tff(c_541,plain,(
    ! [B_88] :
      ( r1_tarski(u1_struct_0(B_88),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_88,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_136,c_144,c_530])).

tff(c_6848,plain,(
    ! [A_424] :
      ( r1_tarski(k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc(k1_tsep_1(A_424,'#skF_6','#skF_5'),'#skF_6')
      | ~ m1_pre_topc('#skF_5',A_424)
      | ~ m1_pre_topc('#skF_6',A_424)
      | ~ l1_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6629,c_541])).

tff(c_31716,plain,(
    r1_tarski(k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')),k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6848])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31721,plain,
    ( k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_6')
    | ~ r1_tarski(k2_struct_0('#skF_6'),k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_31716,c_2])).

tff(c_31743,plain,(
    ~ r1_tarski(k2_struct_0('#skF_6'),k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_31721])).

tff(c_31745,plain,(
    ! [A_421] :
      ( ~ r1_tarski(k2_struct_0('#skF_6'),u1_struct_0(k1_tsep_1(A_421,'#skF_6','#skF_5')))
      | ~ m1_pre_topc('#skF_5',A_421)
      | ~ m1_pre_topc('#skF_6',A_421)
      | ~ l1_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6624,c_31743])).

tff(c_34830,plain,(
    ! [A_1047] :
      ( ~ m1_pre_topc('#skF_6',k1_tsep_1(A_1047,'#skF_6','#skF_5'))
      | ~ v2_pre_topc(A_1047)
      | ~ m1_pre_topc('#skF_5',A_1047)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_6',A_1047)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_1047)
      | v2_struct_0(A_1047) ) ),
    inference(resolution,[status(thm)],[c_34794,c_31745])).

tff(c_35105,plain,(
    ! [A_1053] :
      ( ~ m1_pre_topc('#skF_6',k1_tsep_1(A_1053,'#skF_6','#skF_5'))
      | ~ v2_pre_topc(A_1053)
      | ~ m1_pre_topc('#skF_5',A_1053)
      | ~ m1_pre_topc('#skF_6',A_1053)
      | ~ l1_pre_topc(A_1053)
      | v2_struct_0(A_1053) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_88,c_34830])).

tff(c_35109,plain,(
    ! [A_77] :
      ( ~ m1_pre_topc('#skF_5',A_77)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_6',A_77)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_66,c_35105])).

tff(c_35113,plain,(
    ! [A_1054] :
      ( ~ m1_pre_topc('#skF_5',A_1054)
      | ~ m1_pre_topc('#skF_6',A_1054)
      | ~ l1_pre_topc(A_1054)
      | ~ v2_pre_topc(A_1054)
      | v2_struct_0(A_1054) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_88,c_35109])).

tff(c_35126,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_35113])).

tff(c_35143,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_82,c_35126])).

tff(c_35145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_35143])).

tff(c_35146,plain,(
    k2_xboole_0(k2_struct_0('#skF_6'),k2_struct_0('#skF_5')) = k2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_31721])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35388,plain,(
    ! [A_1060] :
      ( r1_xboole_0(A_1060,k2_struct_0('#skF_5'))
      | ~ r1_xboole_0(A_1060,k2_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35146,c_10])).

tff(c_298,plain,(
    ! [B_126] :
      ( r1_tsep_1('#skF_7',B_126)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_126))
      | ~ l1_struct_0(B_126)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_280])).

tff(c_749,plain,(
    ! [B_158] :
      ( r1_tsep_1('#skF_7',B_158)
      | ~ r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_158))
      | ~ l1_struct_0(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_298])).

tff(c_755,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_749])).

tff(c_767,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_755])).

tff(c_776,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_35406,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_35388,c_776])).

tff(c_35415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_35406])).

tff(c_35441,plain,(
    ! [A_1062] :
      ( ~ m1_pre_topc(k1_tsep_1(A_1062,'#skF_6','#skF_5'),'#skF_6')
      | ~ m1_pre_topc('#skF_5',A_1062)
      | ~ m1_pre_topc('#skF_6',A_1062)
      | ~ l1_pre_topc(A_1062)
      | v2_struct_0(A_1062) ) ),
    inference(splitRight,[status(thm)],[c_6848])).

tff(c_35445,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_35441])).

tff(c_35448,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_462,c_76,c_35445])).

tff(c_35450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_88,c_35448])).

tff(c_35451,plain,(
    r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_64,plain,(
    ! [B_76,A_75] :
      ( r1_tsep_1(B_76,A_75)
      | ~ r1_tsep_1(A_75,B_76)
      | ~ l1_struct_0(B_76)
      | ~ l1_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_35454,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_35451,c_64])).

tff(c_35457,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_700,c_35454])).

tff(c_35459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_35457])).

tff(c_35461,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_35460,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_35556,plain,(
    ! [B_1076,A_1077] :
      ( r1_tsep_1(B_1076,A_1077)
      | ~ r1_tsep_1(A_1077,B_1076)
      | ~ l1_struct_0(B_1076)
      | ~ l1_struct_0(A_1077) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_35558,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_35460,c_35556])).

tff(c_35561,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_35461,c_35558])).

tff(c_35562,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_35561])).

tff(c_35565,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_35562])).

tff(c_35569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35482,c_35565])).

tff(c_35570,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_35561])).

tff(c_35588,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_35570])).

tff(c_35592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35489,c_35588])).

tff(c_35593,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_35594,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_35695,plain,(
    ! [B_1095,A_1096] :
      ( r1_tsep_1(B_1095,A_1096)
      | ~ r1_tsep_1(A_1096,B_1095)
      | ~ l1_struct_0(B_1095)
      | ~ l1_struct_0(A_1096) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_35699,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_35594,c_35695])).

tff(c_35703,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_35593,c_35699])).

tff(c_35704,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_35703])).

tff(c_35707,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_35704])).

tff(c_35711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35628,c_35707])).

tff(c_35712,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_35703])).

tff(c_35716,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_35712])).

tff(c_35720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35625,c_35716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.77/14.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.77/14.08  
% 24.77/14.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.77/14.09  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 24.77/14.09  
% 24.77/14.09  %Foreground sorts:
% 24.77/14.09  
% 24.77/14.09  
% 24.77/14.09  %Background operators:
% 24.77/14.09  
% 24.77/14.09  
% 24.77/14.09  %Foreground operators:
% 24.77/14.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.77/14.09  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 24.77/14.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 24.77/14.09  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 24.77/14.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.77/14.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.77/14.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.77/14.09  tff('#skF_7', type, '#skF_7': $i).
% 24.77/14.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 24.77/14.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.77/14.09  tff('#skF_5', type, '#skF_5': $i).
% 24.77/14.09  tff('#skF_6', type, '#skF_6': $i).
% 24.77/14.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.77/14.09  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 24.77/14.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.77/14.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 24.77/14.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.77/14.09  tff('#skF_4', type, '#skF_4': $i).
% 24.77/14.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.77/14.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 24.77/14.09  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 24.77/14.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.77/14.09  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 24.77/14.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.77/14.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.77/14.09  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 24.77/14.09  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 24.77/14.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.77/14.09  
% 24.96/14.11  tff(f_233, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 24.96/14.11  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 24.96/14.11  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 24.96/14.11  tff(f_160, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 24.96/14.11  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 24.96/14.11  tff(f_130, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 24.96/14.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.96/14.11  tff(f_195, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 24.96/14.11  tff(f_152, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 24.96/14.11  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 24.96/14.11  tff(f_121, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 24.96/14.11  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 24.96/14.11  tff(f_47, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 24.96/14.11  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_78, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_35610, plain, (![B_1083, A_1084]: (l1_pre_topc(B_1083) | ~m1_pre_topc(B_1083, A_1084) | ~l1_pre_topc(A_1084))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.96/14.11  tff(c_35613, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_35610])).
% 24.96/14.11  tff(c_35625, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_35613])).
% 24.96/14.11  tff(c_46, plain, (![A_50]: (l1_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 24.96/14.11  tff(c_86, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_35616, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_35610])).
% 24.96/14.11  tff(c_35628, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_35616])).
% 24.96/14.11  tff(c_82, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_35467, plain, (![B_1064, A_1065]: (l1_pre_topc(B_1064) | ~m1_pre_topc(B_1064, A_1065) | ~l1_pre_topc(A_1065))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.96/14.11  tff(c_35479, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_82, c_35467])).
% 24.96/14.11  tff(c_35489, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_35479])).
% 24.96/14.11  tff(c_35470, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_35467])).
% 24.96/14.11  tff(c_35482, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_35470])).
% 24.96/14.11  tff(c_72, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_98, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_72])).
% 24.96/14.11  tff(c_114, plain, (![B_106, A_107]: (l1_pre_topc(B_106) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.96/14.11  tff(c_117, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_78, c_114])).
% 24.96/14.11  tff(c_129, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_117])).
% 24.96/14.11  tff(c_126, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_82, c_114])).
% 24.96/14.11  tff(c_136, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_126])).
% 24.96/14.11  tff(c_74, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_104, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 24.96/14.11  tff(c_199, plain, (![B_118, A_119]: (r1_tsep_1(B_118, A_119) | ~r1_tsep_1(A_119, B_118) | ~l1_struct_0(B_118) | ~l1_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_160])).
% 24.96/14.11  tff(c_202, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_104, c_199])).
% 24.96/14.11  tff(c_203, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_202])).
% 24.96/14.11  tff(c_206, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_46, c_203])).
% 24.96/14.11  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_206])).
% 24.96/14.11  tff(c_211, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_202])).
% 24.96/14.11  tff(c_218, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_211])).
% 24.96/14.11  tff(c_221, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_218])).
% 24.96/14.11  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_221])).
% 24.96/14.11  tff(c_227, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_211])).
% 24.96/14.11  tff(c_120, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_114])).
% 24.96/14.11  tff(c_132, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_120])).
% 24.96/14.11  tff(c_99, plain, (![A_104]: (u1_struct_0(A_104)=k2_struct_0(A_104) | ~l1_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.96/14.11  tff(c_103, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_46, c_99])).
% 24.96/14.11  tff(c_148, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_132, c_103])).
% 24.96/14.11  tff(c_140, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_129, c_103])).
% 24.96/14.11  tff(c_280, plain, (![A_125, B_126]: (r1_tsep_1(A_125, B_126) | ~r1_xboole_0(u1_struct_0(A_125), u1_struct_0(B_126)) | ~l1_struct_0(B_126) | ~l1_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.96/14.11  tff(c_301, plain, (![A_125]: (r1_tsep_1(A_125, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_125), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_125))), inference(superposition, [status(thm), theory('equality')], [c_140, c_280])).
% 24.96/14.11  tff(c_669, plain, (![A_153]: (r1_tsep_1(A_153, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_153), k2_struct_0('#skF_7')) | ~l1_struct_0(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_301])).
% 24.96/14.11  tff(c_672, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_148, c_669])).
% 24.96/14.11  tff(c_682, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_98, c_672])).
% 24.96/14.11  tff(c_691, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_682])).
% 24.96/14.11  tff(c_694, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_691])).
% 24.96/14.11  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_694])).
% 24.96/14.11  tff(c_700, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_682])).
% 24.96/14.11  tff(c_84, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_88, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_92, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.96/14.11  tff(c_398, plain, (![B_132, C_133, A_134]: (m1_pre_topc(B_132, C_133) | ~r1_tarski(u1_struct_0(B_132), u1_struct_0(C_133)) | ~m1_pre_topc(C_133, A_134) | ~m1_pre_topc(B_132, A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_195])).
% 24.96/14.11  tff(c_442, plain, (![B_136, A_137]: (m1_pre_topc(B_136, B_136) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137))), inference(resolution, [status(thm)], [c_6, c_398])).
% 24.96/14.11  tff(c_450, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_82, c_442])).
% 24.96/14.11  tff(c_462, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_450])).
% 24.96/14.11  tff(c_76, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_58, plain, (![A_72, B_73, C_74]: (m1_pre_topc(k1_tsep_1(A_72, B_73, C_74), A_72) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.96/14.11  tff(c_212, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_202])).
% 24.96/14.11  tff(c_226, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_211])).
% 24.96/14.11  tff(c_144, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_136, c_103])).
% 24.96/14.11  tff(c_247, plain, (![A_123, B_124]: (r1_xboole_0(u1_struct_0(A_123), u1_struct_0(B_124)) | ~r1_tsep_1(A_123, B_124) | ~l1_struct_0(B_124) | ~l1_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.96/14.11  tff(c_262, plain, (![B_124]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_124)) | ~r1_tsep_1('#skF_7', B_124) | ~l1_struct_0(B_124) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_247])).
% 24.96/14.11  tff(c_355, plain, (![B_130]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_130)) | ~r1_tsep_1('#skF_7', B_130) | ~l1_struct_0(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_262])).
% 24.96/14.11  tff(c_361, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_144, c_355])).
% 24.96/14.11  tff(c_369, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_226, c_361])).
% 24.96/14.11  tff(c_94, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.96/14.11  tff(c_66, plain, (![B_81, A_77, C_83]: (m1_pre_topc(B_81, k1_tsep_1(A_77, B_81, C_83)) | ~m1_pre_topc(C_83, A_77) | v2_struct_0(C_83) | ~m1_pre_topc(B_81, A_77) | v2_struct_0(B_81) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_181])).
% 24.96/14.11  tff(c_733, plain, (![A_155, B_156, C_157]: (m1_pre_topc(k1_tsep_1(A_155, B_156, C_157), A_155) | ~m1_pre_topc(C_157, A_155) | v2_struct_0(C_157) | ~m1_pre_topc(B_156, A_155) | v2_struct_0(B_156) | ~l1_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.96/14.11  tff(c_68, plain, (![B_88, C_90, A_84]: (r1_tarski(u1_struct_0(B_88), u1_struct_0(C_90)) | ~m1_pre_topc(B_88, C_90) | ~m1_pre_topc(C_90, A_84) | ~m1_pre_topc(B_88, A_84) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_195])).
% 24.96/14.11  tff(c_2125, plain, (![B_354, A_355, B_356, C_357]: (r1_tarski(u1_struct_0(B_354), u1_struct_0(k1_tsep_1(A_355, B_356, C_357))) | ~m1_pre_topc(B_354, k1_tsep_1(A_355, B_356, C_357)) | ~m1_pre_topc(B_354, A_355) | ~v2_pre_topc(A_355) | ~m1_pre_topc(C_357, A_355) | v2_struct_0(C_357) | ~m1_pre_topc(B_356, A_355) | v2_struct_0(B_356) | ~l1_pre_topc(A_355) | v2_struct_0(A_355))), inference(resolution, [status(thm)], [c_733, c_68])).
% 24.96/14.11  tff(c_34794, plain, (![A_1047, B_1048, C_1049]: (r1_tarski(k2_struct_0('#skF_6'), u1_struct_0(k1_tsep_1(A_1047, B_1048, C_1049))) | ~m1_pre_topc('#skF_6', k1_tsep_1(A_1047, B_1048, C_1049)) | ~m1_pre_topc('#skF_6', A_1047) | ~v2_pre_topc(A_1047) | ~m1_pre_topc(C_1049, A_1047) | v2_struct_0(C_1049) | ~m1_pre_topc(B_1048, A_1047) | v2_struct_0(B_1048) | ~l1_pre_topc(A_1047) | v2_struct_0(A_1047))), inference(superposition, [status(thm), theory('equality')], [c_144, c_2125])).
% 24.96/14.11  tff(c_60, plain, (![A_72, B_73, C_74]: (v1_pre_topc(k1_tsep_1(A_72, B_73, C_74)) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.96/14.11  tff(c_2092, plain, (![A_346, B_347, C_348]: (u1_struct_0(k1_tsep_1(A_346, B_347, C_348))=k2_xboole_0(u1_struct_0(B_347), u1_struct_0(C_348)) | ~m1_pre_topc(k1_tsep_1(A_346, B_347, C_348), A_346) | ~v1_pre_topc(k1_tsep_1(A_346, B_347, C_348)) | v2_struct_0(k1_tsep_1(A_346, B_347, C_348)) | ~m1_pre_topc(C_348, A_346) | v2_struct_0(C_348) | ~m1_pre_topc(B_347, A_346) | v2_struct_0(B_347) | ~l1_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.96/14.11  tff(c_2393, plain, (![A_380, B_381, C_382]: (u1_struct_0(k1_tsep_1(A_380, B_381, C_382))=k2_xboole_0(u1_struct_0(B_381), u1_struct_0(C_382)) | ~v1_pre_topc(k1_tsep_1(A_380, B_381, C_382)) | v2_struct_0(k1_tsep_1(A_380, B_381, C_382)) | ~m1_pre_topc(C_382, A_380) | v2_struct_0(C_382) | ~m1_pre_topc(B_381, A_380) | v2_struct_0(B_381) | ~l1_pre_topc(A_380) | v2_struct_0(A_380))), inference(resolution, [status(thm)], [c_58, c_2092])).
% 24.96/14.11  tff(c_62, plain, (![A_72, B_73, C_74]: (~v2_struct_0(k1_tsep_1(A_72, B_73, C_74)) | ~m1_pre_topc(C_74, A_72) | v2_struct_0(C_74) | ~m1_pre_topc(B_73, A_72) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.96/14.11  tff(c_2710, plain, (![A_384, B_385, C_386]: (u1_struct_0(k1_tsep_1(A_384, B_385, C_386))=k2_xboole_0(u1_struct_0(B_385), u1_struct_0(C_386)) | ~v1_pre_topc(k1_tsep_1(A_384, B_385, C_386)) | ~m1_pre_topc(C_386, A_384) | v2_struct_0(C_386) | ~m1_pre_topc(B_385, A_384) | v2_struct_0(B_385) | ~l1_pre_topc(A_384) | v2_struct_0(A_384))), inference(resolution, [status(thm)], [c_2393, c_62])).
% 24.96/14.11  tff(c_3006, plain, (![A_389, B_390, C_391]: (u1_struct_0(k1_tsep_1(A_389, B_390, C_391))=k2_xboole_0(u1_struct_0(B_390), u1_struct_0(C_391)) | ~m1_pre_topc(C_391, A_389) | v2_struct_0(C_391) | ~m1_pre_topc(B_390, A_389) | v2_struct_0(B_390) | ~l1_pre_topc(A_389) | v2_struct_0(A_389))), inference(resolution, [status(thm)], [c_60, c_2710])).
% 24.96/14.11  tff(c_3302, plain, (![A_389, C_391]: (u1_struct_0(k1_tsep_1(A_389, '#skF_6', C_391))=k2_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(C_391)) | ~m1_pre_topc(C_391, A_389) | v2_struct_0(C_391) | ~m1_pre_topc('#skF_6', A_389) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_389) | v2_struct_0(A_389))), inference(superposition, [status(thm), theory('equality')], [c_144, c_3006])).
% 24.96/14.11  tff(c_6266, plain, (![A_421, C_422]: (u1_struct_0(k1_tsep_1(A_421, '#skF_6', C_422))=k2_xboole_0(k2_struct_0('#skF_6'), u1_struct_0(C_422)) | ~m1_pre_topc(C_422, A_421) | v2_struct_0(C_422) | ~m1_pre_topc('#skF_6', A_421) | ~l1_pre_topc(A_421) | v2_struct_0(A_421))), inference(negUnitSimplification, [status(thm)], [c_84, c_3302])).
% 24.96/14.11  tff(c_6596, plain, (![A_421]: (u1_struct_0(k1_tsep_1(A_421, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_421) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', A_421) | ~l1_pre_topc(A_421) | v2_struct_0(A_421))), inference(superposition, [status(thm), theory('equality')], [c_148, c_6266])).
% 24.96/14.11  tff(c_6624, plain, (![A_421]: (u1_struct_0(k1_tsep_1(A_421, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_421) | ~m1_pre_topc('#skF_6', A_421) | ~l1_pre_topc(A_421) | v2_struct_0(A_421))), inference(negUnitSimplification, [status(thm)], [c_88, c_6596])).
% 24.96/14.11  tff(c_6629, plain, (![A_424]: (u1_struct_0(k1_tsep_1(A_424, '#skF_6', '#skF_5'))=k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', A_424) | ~m1_pre_topc('#skF_6', A_424) | ~l1_pre_topc(A_424) | v2_struct_0(A_424))), inference(negUnitSimplification, [status(thm)], [c_88, c_6596])).
% 24.96/14.11  tff(c_172, plain, (![B_116, A_117]: (v2_pre_topc(B_116) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.96/14.11  tff(c_184, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_82, c_172])).
% 24.96/14.11  tff(c_196, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_184])).
% 24.96/14.11  tff(c_530, plain, (![B_88]: (r1_tarski(u1_struct_0(B_88), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_88, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_462, c_68])).
% 24.96/14.11  tff(c_541, plain, (![B_88]: (r1_tarski(u1_struct_0(B_88), k2_struct_0('#skF_6')) | ~m1_pre_topc(B_88, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_136, c_144, c_530])).
% 24.96/14.11  tff(c_6848, plain, (![A_424]: (r1_tarski(k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')), k2_struct_0('#skF_6')) | ~m1_pre_topc(k1_tsep_1(A_424, '#skF_6', '#skF_5'), '#skF_6') | ~m1_pre_topc('#skF_5', A_424) | ~m1_pre_topc('#skF_6', A_424) | ~l1_pre_topc(A_424) | v2_struct_0(A_424))), inference(superposition, [status(thm), theory('equality')], [c_6629, c_541])).
% 24.96/14.11  tff(c_31716, plain, (r1_tarski(k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')), k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_6848])).
% 24.96/14.11  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.96/14.11  tff(c_31721, plain, (k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_6') | ~r1_tarski(k2_struct_0('#skF_6'), k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_31716, c_2])).
% 24.96/14.11  tff(c_31743, plain, (~r1_tarski(k2_struct_0('#skF_6'), k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_31721])).
% 24.96/14.11  tff(c_31745, plain, (![A_421]: (~r1_tarski(k2_struct_0('#skF_6'), u1_struct_0(k1_tsep_1(A_421, '#skF_6', '#skF_5'))) | ~m1_pre_topc('#skF_5', A_421) | ~m1_pre_topc('#skF_6', A_421) | ~l1_pre_topc(A_421) | v2_struct_0(A_421))), inference(superposition, [status(thm), theory('equality')], [c_6624, c_31743])).
% 24.96/14.11  tff(c_34830, plain, (![A_1047]: (~m1_pre_topc('#skF_6', k1_tsep_1(A_1047, '#skF_6', '#skF_5')) | ~v2_pre_topc(A_1047) | ~m1_pre_topc('#skF_5', A_1047) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', A_1047) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_1047) | v2_struct_0(A_1047))), inference(resolution, [status(thm)], [c_34794, c_31745])).
% 24.96/14.11  tff(c_35105, plain, (![A_1053]: (~m1_pre_topc('#skF_6', k1_tsep_1(A_1053, '#skF_6', '#skF_5')) | ~v2_pre_topc(A_1053) | ~m1_pre_topc('#skF_5', A_1053) | ~m1_pre_topc('#skF_6', A_1053) | ~l1_pre_topc(A_1053) | v2_struct_0(A_1053))), inference(negUnitSimplification, [status(thm)], [c_84, c_88, c_34830])).
% 24.96/14.11  tff(c_35109, plain, (![A_77]: (~m1_pre_topc('#skF_5', A_77) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', A_77) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_66, c_35105])).
% 24.96/14.11  tff(c_35113, plain, (![A_1054]: (~m1_pre_topc('#skF_5', A_1054) | ~m1_pre_topc('#skF_6', A_1054) | ~l1_pre_topc(A_1054) | ~v2_pre_topc(A_1054) | v2_struct_0(A_1054))), inference(negUnitSimplification, [status(thm)], [c_84, c_88, c_35109])).
% 24.96/14.11  tff(c_35126, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_35113])).
% 24.96/14.11  tff(c_35143, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_82, c_35126])).
% 24.96/14.11  tff(c_35145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_35143])).
% 24.96/14.11  tff(c_35146, plain, (k2_xboole_0(k2_struct_0('#skF_6'), k2_struct_0('#skF_5'))=k2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_31721])).
% 24.96/14.11  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.96/14.11  tff(c_35388, plain, (![A_1060]: (r1_xboole_0(A_1060, k2_struct_0('#skF_5')) | ~r1_xboole_0(A_1060, k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_35146, c_10])).
% 24.96/14.11  tff(c_298, plain, (![B_126]: (r1_tsep_1('#skF_7', B_126) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_126)) | ~l1_struct_0(B_126) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_280])).
% 24.96/14.11  tff(c_749, plain, (![B_158]: (r1_tsep_1('#skF_7', B_158) | ~r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_158)) | ~l1_struct_0(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_298])).
% 24.96/14.11  tff(c_755, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_148, c_749])).
% 24.96/14.11  tff(c_767, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_700, c_755])).
% 24.96/14.11  tff(c_776, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_767])).
% 24.96/14.11  tff(c_35406, plain, (~r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_35388, c_776])).
% 24.96/14.11  tff(c_35415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_35406])).
% 24.96/14.11  tff(c_35441, plain, (![A_1062]: (~m1_pre_topc(k1_tsep_1(A_1062, '#skF_6', '#skF_5'), '#skF_6') | ~m1_pre_topc('#skF_5', A_1062) | ~m1_pre_topc('#skF_6', A_1062) | ~l1_pre_topc(A_1062) | v2_struct_0(A_1062))), inference(splitRight, [status(thm)], [c_6848])).
% 24.96/14.11  tff(c_35445, plain, (~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_58, c_35441])).
% 24.96/14.11  tff(c_35448, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_462, c_76, c_35445])).
% 24.96/14.11  tff(c_35450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_88, c_35448])).
% 24.96/14.11  tff(c_35451, plain, (r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_767])).
% 24.96/14.11  tff(c_64, plain, (![B_76, A_75]: (r1_tsep_1(B_76, A_75) | ~r1_tsep_1(A_75, B_76) | ~l1_struct_0(B_76) | ~l1_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_160])).
% 24.96/14.11  tff(c_35454, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_35451, c_64])).
% 24.96/14.11  tff(c_35457, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_700, c_35454])).
% 24.96/14.11  tff(c_35459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_35457])).
% 24.96/14.11  tff(c_35461, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 24.96/14.11  tff(c_35460, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 24.96/14.11  tff(c_35556, plain, (![B_1076, A_1077]: (r1_tsep_1(B_1076, A_1077) | ~r1_tsep_1(A_1077, B_1076) | ~l1_struct_0(B_1076) | ~l1_struct_0(A_1077))), inference(cnfTransformation, [status(thm)], [f_160])).
% 24.96/14.11  tff(c_35558, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_35460, c_35556])).
% 24.96/14.11  tff(c_35561, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_35461, c_35558])).
% 24.96/14.11  tff(c_35562, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_35561])).
% 24.96/14.11  tff(c_35565, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_35562])).
% 24.96/14.11  tff(c_35569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35482, c_35565])).
% 24.96/14.11  tff(c_35570, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_35561])).
% 24.96/14.11  tff(c_35588, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_46, c_35570])).
% 24.96/14.11  tff(c_35592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35489, c_35588])).
% 24.96/14.11  tff(c_35593, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 24.96/14.11  tff(c_35594, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 24.96/14.11  tff(c_35695, plain, (![B_1095, A_1096]: (r1_tsep_1(B_1095, A_1096) | ~r1_tsep_1(A_1096, B_1095) | ~l1_struct_0(B_1095) | ~l1_struct_0(A_1096))), inference(cnfTransformation, [status(thm)], [f_160])).
% 24.96/14.11  tff(c_35699, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_35594, c_35695])).
% 24.96/14.11  tff(c_35703, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_35593, c_35699])).
% 24.96/14.11  tff(c_35704, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_35703])).
% 24.96/14.11  tff(c_35707, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_35704])).
% 24.96/14.11  tff(c_35711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35628, c_35707])).
% 24.96/14.11  tff(c_35712, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_35703])).
% 24.96/14.11  tff(c_35716, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_46, c_35712])).
% 24.96/14.11  tff(c_35720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35625, c_35716])).
% 24.96/14.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.96/14.11  
% 24.96/14.11  Inference rules
% 24.96/14.11  ----------------------
% 24.96/14.11  #Ref     : 4
% 24.96/14.11  #Sup     : 10675
% 24.96/14.11  #Fact    : 2
% 24.96/14.11  #Define  : 0
% 24.96/14.11  #Split   : 103
% 24.96/14.11  #Chain   : 0
% 24.96/14.11  #Close   : 0
% 24.96/14.11  
% 24.96/14.11  Ordering : KBO
% 24.96/14.11  
% 24.96/14.11  Simplification rules
% 24.96/14.11  ----------------------
% 24.96/14.11  #Subsume      : 1419
% 24.96/14.11  #Demod        : 3425
% 24.96/14.11  #Tautology    : 759
% 24.96/14.11  #SimpNegUnit  : 2441
% 24.96/14.11  #BackRed      : 8
% 24.96/14.11  
% 24.96/14.11  #Partial instantiations: 0
% 24.96/14.11  #Strategies tried      : 1
% 24.96/14.11  
% 24.96/14.11  Timing (in seconds)
% 24.96/14.11  ----------------------
% 24.96/14.12  Preprocessing        : 0.39
% 24.96/14.12  Parsing              : 0.20
% 24.96/14.12  CNF conversion       : 0.03
% 24.96/14.12  Main loop            : 12.83
% 24.96/14.12  Inferencing          : 2.25
% 24.96/14.12  Reduction            : 3.66
% 24.96/14.12  Demodulation         : 2.61
% 24.96/14.12  BG Simplification    : 0.33
% 24.96/14.12  Subsumption          : 5.90
% 24.96/14.12  Abstraction          : 0.38
% 24.96/14.12  MUC search           : 0.00
% 24.96/14.12  Cooper               : 0.00
% 24.96/14.12  Total                : 13.27
% 24.96/14.12  Index Insertion      : 0.00
% 24.96/14.12  Index Deletion       : 0.00
% 24.96/14.12  Index Matching       : 0.00
% 24.96/14.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
