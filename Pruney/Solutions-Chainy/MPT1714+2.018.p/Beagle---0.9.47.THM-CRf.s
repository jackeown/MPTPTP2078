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
% DateTime   : Thu Dec  3 10:26:35 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 638 expanded)
%              Number of leaves         :   39 ( 215 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 (2287 expanded)
%              Number of equality atoms :   11 (  77 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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

tff(f_109,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_81,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_86,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_74,plain,(
    m1_pre_topc('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2132,plain,(
    ! [B_219,A_220] :
      ( l1_pre_topc(B_219)
      | ~ m1_pre_topc(B_219,A_220)
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2135,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_2132])).

tff(c_2147,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2135])).

tff(c_58,plain,(
    ! [A_55] :
      ( l1_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    m1_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2138,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_2132])).

tff(c_2150,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2138])).

tff(c_78,plain,(
    m1_pre_topc('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2012,plain,(
    ! [B_198,A_199] :
      ( l1_pre_topc(B_198)
      | ~ m1_pre_topc(B_198,A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2024,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_2012])).

tff(c_2034,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2024])).

tff(c_2015,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_2012])).

tff(c_2027,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2015])).

tff(c_70,plain,
    ( ~ r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_tsep_1('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_97,plain,(
    ~ r1_tsep_1('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_109,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_112,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_124,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_112])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_109])).

tff(c_131,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_121])).

tff(c_68,plain,
    ( r1_tsep_1('#skF_10','#skF_9')
    | r1_tsep_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_98,plain,(
    r1_tsep_1('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_183,plain,(
    ! [B_95,A_96] :
      ( r1_tsep_1(B_95,A_96)
      | ~ r1_tsep_1(A_96,B_95)
      | ~ l1_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_186,plain,
    ( r1_tsep_1('#skF_10','#skF_9')
    | ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_98,c_183])).

tff(c_187,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_190,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_190])).

tff(c_195,plain,
    ( ~ l1_struct_0('#skF_10')
    | r1_tsep_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_211,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_214,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_211])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_214])).

tff(c_220,plain,(
    l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_109])).

tff(c_127,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_115])).

tff(c_92,plain,(
    ! [A_76] :
      ( u1_struct_0(A_76) = k2_struct_0(A_76)
      | ~ l1_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_58,c_92])).

tff(c_143,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_127,c_96])).

tff(c_135,plain,(
    u1_struct_0('#skF_10') = k2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_124,c_96])).

tff(c_295,plain,(
    ! [A_105,B_106] :
      ( r1_tsep_1(A_105,B_106)
      | ~ r1_xboole_0(u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ l1_struct_0(B_106)
      | ~ l1_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_316,plain,(
    ! [A_105] :
      ( r1_tsep_1(A_105,'#skF_10')
      | ~ r1_xboole_0(u1_struct_0(A_105),k2_struct_0('#skF_10'))
      | ~ l1_struct_0('#skF_10')
      | ~ l1_struct_0(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_295])).

tff(c_543,plain,(
    ! [A_119] :
      ( r1_tsep_1(A_119,'#skF_10')
      | ~ r1_xboole_0(u1_struct_0(A_119),k2_struct_0('#skF_10'))
      | ~ l1_struct_0(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_316])).

tff(c_546,plain,
    ( r1_tsep_1('#skF_8','#skF_10')
    | ~ r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_10'))
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_543])).

tff(c_556,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_10'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_546])).

tff(c_563,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_582,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_563])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_582])).

tff(c_588,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_72,plain,(
    m1_pre_topc('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_231,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(k2_struct_0(B_100),k2_struct_0(A_101))
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(B_100)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1902,plain,(
    ! [B_192,A_193] :
      ( k3_xboole_0(k2_struct_0(B_192),k2_struct_0(A_193)) = k2_struct_0(B_192)
      | ~ m1_pre_topc(B_192,A_193)
      | ~ l1_pre_topc(B_192)
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_231,c_26])).

tff(c_160,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_3'(A_88,B_89),B_89)
      | r1_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1088,plain,(
    ! [A_162,A_163,B_164] :
      ( r2_hidden('#skF_3'(A_162,k3_xboole_0(A_163,B_164)),B_164)
      | r1_xboole_0(A_162,k3_xboole_0(A_163,B_164)) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_196,plain,(
    l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_139,plain,(
    u1_struct_0('#skF_9') = k2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_131,c_96])).

tff(c_236,plain,(
    ! [A_102,B_103] :
      ( r1_xboole_0(u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ r1_tsep_1(A_102,B_103)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_247,plain,(
    ! [B_103] :
      ( r1_xboole_0(k2_struct_0('#skF_9'),u1_struct_0(B_103))
      | ~ r1_tsep_1('#skF_9',B_103)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_236])).

tff(c_272,plain,(
    ! [B_104] :
      ( r1_xboole_0(k2_struct_0('#skF_9'),u1_struct_0(B_104))
      | ~ r1_tsep_1('#skF_9',B_104)
      | ~ l1_struct_0(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_247])).

tff(c_283,plain,
    ( r1_xboole_0(k2_struct_0('#skF_9'),k2_struct_0('#skF_10'))
    | ~ r1_tsep_1('#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_272])).

tff(c_291,plain,(
    r1_xboole_0(k2_struct_0('#skF_9'),k2_struct_0('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_98,c_283])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_333,plain,(
    ! [C_107] :
      ( ~ r2_hidden(C_107,k2_struct_0('#skF_10'))
      | ~ r2_hidden(C_107,k2_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_291,c_20])).

tff(c_342,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_3'(k2_struct_0('#skF_10'),B_8),k2_struct_0('#skF_9'))
      | r1_xboole_0(k2_struct_0('#skF_10'),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_1115,plain,(
    ! [A_163] : r1_xboole_0(k2_struct_0('#skF_10'),k3_xboole_0(A_163,k2_struct_0('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_1088,c_342])).

tff(c_1916,plain,(
    ! [B_192] :
      ( r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0(B_192))
      | ~ m1_pre_topc(B_192,'#skF_9')
      | ~ l1_pre_topc(B_192)
      | ~ l1_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_1115])).

tff(c_1968,plain,(
    ! [B_194] :
      ( r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0(B_194))
      | ~ m1_pre_topc(B_194,'#skF_9')
      | ~ l1_pre_topc(B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1916])).

tff(c_253,plain,(
    ! [B_103] :
      ( r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_103))
      | ~ r1_tsep_1('#skF_10',B_103)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_236])).

tff(c_789,plain,(
    ! [B_137] :
      ( r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_137))
      | ~ r1_tsep_1('#skF_10',B_137)
      | ~ l1_struct_0(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_253])).

tff(c_797,plain,
    ( r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8'))
    | ~ r1_tsep_1('#skF_10','#skF_8')
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_789])).

tff(c_810,plain,
    ( r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8'))
    | ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_797])).

tff(c_819,plain,(
    ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_313,plain,(
    ! [B_106] :
      ( r1_tsep_1('#skF_10',B_106)
      | ~ r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_106))
      | ~ l1_struct_0(B_106)
      | ~ l1_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_295])).

tff(c_360,plain,(
    ! [B_108] :
      ( r1_tsep_1('#skF_10',B_108)
      | ~ r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_108))
      | ~ l1_struct_0(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_313])).

tff(c_363,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_360])).

tff(c_844,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_363])).

tff(c_845,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_844])).

tff(c_1971,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_9')
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_1968,c_845])).

tff(c_1983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_1971])).

tff(c_1985,plain,(
    r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_66,plain,(
    ! [B_63,A_62] :
      ( r1_tsep_1(B_63,A_62)
      | ~ r1_tsep_1(A_62,B_63)
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2004,plain,
    ( r1_tsep_1('#skF_8','#skF_10')
    | ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_1985,c_66])).

tff(c_2007,plain,(
    r1_tsep_1('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_588,c_2004])).

tff(c_2009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_2007])).

tff(c_2011,plain,(
    ~ r1_tsep_1('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2010,plain,(
    r1_tsep_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2096,plain,(
    ! [B_216,A_217] :
      ( r1_tsep_1(B_216,A_217)
      | ~ r1_tsep_1(A_217,B_216)
      | ~ l1_struct_0(B_216)
      | ~ l1_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2098,plain,
    ( r1_tsep_1('#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2010,c_2096])).

tff(c_2101,plain,
    ( ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_2011,c_2098])).

tff(c_2102,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2101])).

tff(c_2105,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_2102])).

tff(c_2109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_2105])).

tff(c_2110,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2101])).

tff(c_2119,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_2110])).

tff(c_2123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_2119])).

tff(c_2124,plain,(
    ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2125,plain,(
    r1_tsep_1('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2211,plain,(
    ! [B_236,A_237] :
      ( r1_tsep_1(B_236,A_237)
      | ~ r1_tsep_1(A_237,B_236)
      | ~ l1_struct_0(B_236)
      | ~ l1_struct_0(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2215,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2125,c_2211])).

tff(c_2219,plain,
    ( ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2124,c_2215])).

tff(c_2220,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2219])).

tff(c_2223,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_2220])).

tff(c_2227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2223])).

tff(c_2228,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_2219])).

tff(c_2232,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_2228])).

tff(c_2236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/2.11  
% 4.59/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/2.11  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5
% 4.59/2.11  
% 4.59/2.11  %Foreground sorts:
% 4.59/2.11  
% 4.59/2.11  
% 4.59/2.11  %Background operators:
% 4.59/2.11  
% 4.59/2.11  
% 4.59/2.11  %Foreground operators:
% 4.59/2.11  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.59/2.11  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.59/2.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.59/2.11  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.59/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.59/2.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.59/2.11  tff('#skF_7', type, '#skF_7': $i).
% 4.59/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.59/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/2.11  tff('#skF_10', type, '#skF_10': $i).
% 4.59/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.59/2.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.59/2.11  tff('#skF_9', type, '#skF_9': $i).
% 4.59/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/2.11  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.59/2.11  tff('#skF_8', type, '#skF_8': $i).
% 4.59/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/2.11  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.59/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.59/2.11  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.59/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.59/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.59/2.11  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.59/2.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.59/2.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.59/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/2.11  
% 4.76/2.13  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 4.76/2.13  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.76/2.13  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.76/2.13  tff(f_109, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 4.76/2.13  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.76/2.13  tff(f_101, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 4.76/2.13  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 4.76/2.13  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.76/2.13  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.76/2.13  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.76/2.13  tff(c_86, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_74, plain, (m1_pre_topc('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_2132, plain, (![B_219, A_220]: (l1_pre_topc(B_219) | ~m1_pre_topc(B_219, A_220) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.76/2.13  tff(c_2135, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_74, c_2132])).
% 4.76/2.13  tff(c_2147, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2135])).
% 4.76/2.13  tff(c_58, plain, (![A_55]: (l1_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.76/2.13  tff(c_82, plain, (m1_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_2138, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_2132])).
% 4.76/2.13  tff(c_2150, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2138])).
% 4.76/2.13  tff(c_78, plain, (m1_pre_topc('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_2012, plain, (![B_198, A_199]: (l1_pre_topc(B_198) | ~m1_pre_topc(B_198, A_199) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.76/2.13  tff(c_2024, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_78, c_2012])).
% 4.76/2.13  tff(c_2034, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2024])).
% 4.76/2.13  tff(c_2015, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_74, c_2012])).
% 4.76/2.13  tff(c_2027, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2015])).
% 4.76/2.13  tff(c_70, plain, (~r1_tsep_1('#skF_10', '#skF_8') | ~r1_tsep_1('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_97, plain, (~r1_tsep_1('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_70])).
% 4.76/2.13  tff(c_109, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.76/2.13  tff(c_112, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_74, c_109])).
% 4.76/2.13  tff(c_124, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_112])).
% 4.76/2.13  tff(c_121, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_78, c_109])).
% 4.76/2.13  tff(c_131, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_121])).
% 4.76/2.13  tff(c_68, plain, (r1_tsep_1('#skF_10', '#skF_9') | r1_tsep_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_98, plain, (r1_tsep_1('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_68])).
% 4.76/2.13  tff(c_183, plain, (![B_95, A_96]: (r1_tsep_1(B_95, A_96) | ~r1_tsep_1(A_96, B_95) | ~l1_struct_0(B_95) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.76/2.13  tff(c_186, plain, (r1_tsep_1('#skF_10', '#skF_9') | ~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_98, c_183])).
% 4.76/2.13  tff(c_187, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_186])).
% 4.76/2.13  tff(c_190, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_58, c_187])).
% 4.76/2.13  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_190])).
% 4.76/2.13  tff(c_195, plain, (~l1_struct_0('#skF_10') | r1_tsep_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_186])).
% 4.76/2.13  tff(c_211, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_195])).
% 4.76/2.13  tff(c_214, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_58, c_211])).
% 4.76/2.13  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_214])).
% 4.76/2.13  tff(c_220, plain, (l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_195])).
% 4.76/2.13  tff(c_115, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_109])).
% 4.76/2.13  tff(c_127, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_115])).
% 4.76/2.13  tff(c_92, plain, (![A_76]: (u1_struct_0(A_76)=k2_struct_0(A_76) | ~l1_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.76/2.13  tff(c_96, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_58, c_92])).
% 4.76/2.13  tff(c_143, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_127, c_96])).
% 4.76/2.13  tff(c_135, plain, (u1_struct_0('#skF_10')=k2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_124, c_96])).
% 4.76/2.13  tff(c_295, plain, (![A_105, B_106]: (r1_tsep_1(A_105, B_106) | ~r1_xboole_0(u1_struct_0(A_105), u1_struct_0(B_106)) | ~l1_struct_0(B_106) | ~l1_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.76/2.13  tff(c_316, plain, (![A_105]: (r1_tsep_1(A_105, '#skF_10') | ~r1_xboole_0(u1_struct_0(A_105), k2_struct_0('#skF_10')) | ~l1_struct_0('#skF_10') | ~l1_struct_0(A_105))), inference(superposition, [status(thm), theory('equality')], [c_135, c_295])).
% 4.76/2.13  tff(c_543, plain, (![A_119]: (r1_tsep_1(A_119, '#skF_10') | ~r1_xboole_0(u1_struct_0(A_119), k2_struct_0('#skF_10')) | ~l1_struct_0(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_316])).
% 4.76/2.13  tff(c_546, plain, (r1_tsep_1('#skF_8', '#skF_10') | ~r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_10')) | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_143, c_543])).
% 4.76/2.13  tff(c_556, plain, (~r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_10')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_97, c_546])).
% 4.76/2.13  tff(c_563, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_556])).
% 4.76/2.13  tff(c_582, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_58, c_563])).
% 4.76/2.13  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_582])).
% 4.76/2.13  tff(c_588, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_556])).
% 4.76/2.13  tff(c_72, plain, (m1_pre_topc('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/2.13  tff(c_231, plain, (![B_100, A_101]: (r1_tarski(k2_struct_0(B_100), k2_struct_0(A_101)) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(B_100) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.76/2.13  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.76/2.13  tff(c_1902, plain, (![B_192, A_193]: (k3_xboole_0(k2_struct_0(B_192), k2_struct_0(A_193))=k2_struct_0(B_192) | ~m1_pre_topc(B_192, A_193) | ~l1_pre_topc(B_192) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_231, c_26])).
% 4.76/2.13  tff(c_160, plain, (![A_88, B_89]: (r2_hidden('#skF_3'(A_88, B_89), B_89) | r1_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.76/2.13  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/2.13  tff(c_1088, plain, (![A_162, A_163, B_164]: (r2_hidden('#skF_3'(A_162, k3_xboole_0(A_163, B_164)), B_164) | r1_xboole_0(A_162, k3_xboole_0(A_163, B_164)))), inference(resolution, [status(thm)], [c_160, c_4])).
% 4.76/2.13  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.76/2.13  tff(c_196, plain, (l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_186])).
% 4.76/2.13  tff(c_139, plain, (u1_struct_0('#skF_9')=k2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_131, c_96])).
% 4.76/2.13  tff(c_236, plain, (![A_102, B_103]: (r1_xboole_0(u1_struct_0(A_102), u1_struct_0(B_103)) | ~r1_tsep_1(A_102, B_103) | ~l1_struct_0(B_103) | ~l1_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.76/2.13  tff(c_247, plain, (![B_103]: (r1_xboole_0(k2_struct_0('#skF_9'), u1_struct_0(B_103)) | ~r1_tsep_1('#skF_9', B_103) | ~l1_struct_0(B_103) | ~l1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_236])).
% 4.76/2.13  tff(c_272, plain, (![B_104]: (r1_xboole_0(k2_struct_0('#skF_9'), u1_struct_0(B_104)) | ~r1_tsep_1('#skF_9', B_104) | ~l1_struct_0(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_247])).
% 4.76/2.13  tff(c_283, plain, (r1_xboole_0(k2_struct_0('#skF_9'), k2_struct_0('#skF_10')) | ~r1_tsep_1('#skF_9', '#skF_10') | ~l1_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_135, c_272])).
% 4.76/2.13  tff(c_291, plain, (r1_xboole_0(k2_struct_0('#skF_9'), k2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_98, c_283])).
% 4.76/2.13  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.76/2.13  tff(c_333, plain, (![C_107]: (~r2_hidden(C_107, k2_struct_0('#skF_10')) | ~r2_hidden(C_107, k2_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_291, c_20])).
% 4.76/2.13  tff(c_342, plain, (![B_8]: (~r2_hidden('#skF_3'(k2_struct_0('#skF_10'), B_8), k2_struct_0('#skF_9')) | r1_xboole_0(k2_struct_0('#skF_10'), B_8))), inference(resolution, [status(thm)], [c_24, c_333])).
% 4.76/2.13  tff(c_1115, plain, (![A_163]: (r1_xboole_0(k2_struct_0('#skF_10'), k3_xboole_0(A_163, k2_struct_0('#skF_9'))))), inference(resolution, [status(thm)], [c_1088, c_342])).
% 4.76/2.13  tff(c_1916, plain, (![B_192]: (r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0(B_192)) | ~m1_pre_topc(B_192, '#skF_9') | ~l1_pre_topc(B_192) | ~l1_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1902, c_1115])).
% 4.76/2.13  tff(c_1968, plain, (![B_194]: (r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0(B_194)) | ~m1_pre_topc(B_194, '#skF_9') | ~l1_pre_topc(B_194))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_1916])).
% 4.76/2.13  tff(c_253, plain, (![B_103]: (r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_103)) | ~r1_tsep_1('#skF_10', B_103) | ~l1_struct_0(B_103) | ~l1_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_236])).
% 4.76/2.13  tff(c_789, plain, (![B_137]: (r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_137)) | ~r1_tsep_1('#skF_10', B_137) | ~l1_struct_0(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_253])).
% 4.76/2.13  tff(c_797, plain, (r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8')) | ~r1_tsep_1('#skF_10', '#skF_8') | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_143, c_789])).
% 4.76/2.13  tff(c_810, plain, (r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8')) | ~r1_tsep_1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_797])).
% 4.76/2.13  tff(c_819, plain, (~r1_tsep_1('#skF_10', '#skF_8')), inference(splitLeft, [status(thm)], [c_810])).
% 4.76/2.13  tff(c_313, plain, (![B_106]: (r1_tsep_1('#skF_10', B_106) | ~r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_106)) | ~l1_struct_0(B_106) | ~l1_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_295])).
% 4.76/2.13  tff(c_360, plain, (![B_108]: (r1_tsep_1('#skF_10', B_108) | ~r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_108)) | ~l1_struct_0(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_313])).
% 4.76/2.13  tff(c_363, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_143, c_360])).
% 4.76/2.13  tff(c_844, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_363])).
% 4.76/2.13  tff(c_845, plain, (~r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_819, c_844])).
% 4.76/2.13  tff(c_1971, plain, (~m1_pre_topc('#skF_8', '#skF_9') | ~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_1968, c_845])).
% 4.76/2.13  tff(c_1983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_1971])).
% 4.76/2.13  tff(c_1985, plain, (r1_tsep_1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_810])).
% 4.76/2.13  tff(c_66, plain, (![B_63, A_62]: (r1_tsep_1(B_63, A_62) | ~r1_tsep_1(A_62, B_63) | ~l1_struct_0(B_63) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.76/2.13  tff(c_2004, plain, (r1_tsep_1('#skF_8', '#skF_10') | ~l1_struct_0('#skF_8') | ~l1_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_1985, c_66])).
% 4.76/2.13  tff(c_2007, plain, (r1_tsep_1('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_588, c_2004])).
% 4.76/2.13  tff(c_2009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_2007])).
% 4.76/2.13  tff(c_2011, plain, (~r1_tsep_1('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_68])).
% 4.76/2.13  tff(c_2010, plain, (r1_tsep_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 4.76/2.13  tff(c_2096, plain, (![B_216, A_217]: (r1_tsep_1(B_216, A_217) | ~r1_tsep_1(A_217, B_216) | ~l1_struct_0(B_216) | ~l1_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.76/2.13  tff(c_2098, plain, (r1_tsep_1('#skF_9', '#skF_10') | ~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2010, c_2096])).
% 4.76/2.13  tff(c_2101, plain, (~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_2011, c_2098])).
% 4.76/2.13  tff(c_2102, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_2101])).
% 4.76/2.13  tff(c_2105, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_58, c_2102])).
% 4.76/2.13  tff(c_2109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2027, c_2105])).
% 4.76/2.13  tff(c_2110, plain, (~l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_2101])).
% 4.76/2.13  tff(c_2119, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_58, c_2110])).
% 4.76/2.13  tff(c_2123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2034, c_2119])).
% 4.76/2.13  tff(c_2124, plain, (~r1_tsep_1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 4.76/2.13  tff(c_2125, plain, (r1_tsep_1('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_70])).
% 4.76/2.13  tff(c_2211, plain, (![B_236, A_237]: (r1_tsep_1(B_236, A_237) | ~r1_tsep_1(A_237, B_236) | ~l1_struct_0(B_236) | ~l1_struct_0(A_237))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.76/2.13  tff(c_2215, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_2125, c_2211])).
% 4.76/2.13  tff(c_2219, plain, (~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2124, c_2215])).
% 4.76/2.13  tff(c_2220, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_2219])).
% 4.76/2.13  tff(c_2223, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_58, c_2220])).
% 4.76/2.13  tff(c_2227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2223])).
% 4.76/2.13  tff(c_2228, plain, (~l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_2219])).
% 4.76/2.13  tff(c_2232, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_58, c_2228])).
% 4.76/2.13  tff(c_2236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2232])).
% 4.76/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/2.13  
% 4.76/2.13  Inference rules
% 4.76/2.13  ----------------------
% 4.76/2.13  #Ref     : 0
% 4.76/2.13  #Sup     : 423
% 4.76/2.13  #Fact    : 0
% 4.76/2.13  #Define  : 0
% 4.76/2.13  #Split   : 22
% 4.76/2.13  #Chain   : 0
% 4.76/2.13  #Close   : 0
% 4.76/2.13  
% 4.76/2.13  Ordering : KBO
% 4.76/2.13  
% 4.76/2.13  Simplification rules
% 4.76/2.13  ----------------------
% 4.76/2.13  #Subsume      : 69
% 4.76/2.13  #Demod        : 175
% 4.76/2.13  #Tautology    : 59
% 4.76/2.13  #SimpNegUnit  : 42
% 4.76/2.13  #BackRed      : 0
% 4.76/2.13  
% 4.76/2.13  #Partial instantiations: 0
% 4.76/2.13  #Strategies tried      : 1
% 4.76/2.13  
% 4.76/2.13  Timing (in seconds)
% 4.76/2.13  ----------------------
% 4.76/2.13  Preprocessing        : 0.59
% 4.76/2.14  Parsing              : 0.28
% 4.76/2.14  CNF conversion       : 0.05
% 4.76/2.14  Main loop            : 0.70
% 4.76/2.14  Inferencing          : 0.23
% 4.76/2.14  Reduction            : 0.21
% 4.76/2.14  Demodulation         : 0.14
% 4.76/2.14  BG Simplification    : 0.04
% 4.76/2.14  Subsumption          : 0.16
% 4.76/2.14  Abstraction          : 0.04
% 4.76/2.14  MUC search           : 0.00
% 4.76/2.14  Cooper               : 0.00
% 4.76/2.14  Total                : 1.34
% 4.76/2.14  Index Insertion      : 0.00
% 4.76/2.14  Index Deletion       : 0.00
% 4.76/2.14  Index Matching       : 0.00
% 4.76/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
