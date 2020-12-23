%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:38 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 355 expanded)
%              Number of leaves         :   39 ( 130 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 (1270 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_86,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_78,plain,(
    m1_pre_topc('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4317,plain,(
    ! [B_340,A_341] :
      ( l1_pre_topc(B_340)
      | ~ m1_pre_topc(B_340,A_341)
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4329,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_4317])).

tff(c_4339,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4329])).

tff(c_58,plain,(
    ! [A_55] :
      ( l1_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_74,plain,(
    m1_pre_topc('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4320,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_4317])).

tff(c_4332,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4320])).

tff(c_4218,plain,(
    ! [B_320,A_321] :
      ( l1_pre_topc(B_320)
      | ~ m1_pre_topc(B_320,A_321)
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4221,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_4218])).

tff(c_4233,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4221])).

tff(c_82,plain,(
    m1_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4224,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_4218])).

tff(c_4236,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4224])).

tff(c_109,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_109])).

tff(c_127,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_115])).

tff(c_72,plain,(
    m1_pre_topc('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_109])).

tff(c_131,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_121])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_368,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(k2_struct_0(B_107),k2_struct_0(A_108))
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(B_107)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1586,plain,(
    ! [B_162,A_163] :
      ( k2_xboole_0(k2_struct_0(B_162),k2_struct_0(A_163)) = k2_struct_0(A_163)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(B_162)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_368,c_26])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1716,plain,(
    ! [D_171,B_172,A_173] :
      ( ~ r2_hidden(D_171,k2_struct_0(B_172))
      | r2_hidden(D_171,k2_struct_0(A_173))
      | ~ m1_pre_topc(B_172,A_173)
      | ~ l1_pre_topc(B_172)
      | ~ l1_pre_topc(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_6])).

tff(c_4072,plain,(
    ! [B_310,B_311,A_312] :
      ( r2_hidden('#skF_3'(k2_struct_0(B_310),B_311),k2_struct_0(A_312))
      | ~ m1_pre_topc(B_310,A_312)
      | ~ l1_pre_topc(B_310)
      | ~ l1_pre_topc(A_312)
      | r1_xboole_0(k2_struct_0(B_310),B_311) ) ),
    inference(resolution,[status(thm)],[c_24,c_1716])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_124,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_112])).

tff(c_70,plain,
    ( r1_tsep_1('#skF_10','#skF_9')
    | r1_tsep_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_97,plain,(
    r1_tsep_1('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_163,plain,(
    ! [B_95,A_96] :
      ( r1_tsep_1(B_95,A_96)
      | ~ r1_tsep_1(A_96,B_95)
      | ~ l1_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_166,plain,
    ( r1_tsep_1('#skF_10','#skF_9')
    | ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_97,c_163])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_170])).

tff(c_175,plain,
    ( ~ l1_struct_0('#skF_10')
    | r1_tsep_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_201,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_204,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_204])).

tff(c_210,plain,(
    l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_175])).

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

tff(c_135,plain,(
    u1_struct_0('#skF_10') = k2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_124,c_96])).

tff(c_176,plain,(
    l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_139,plain,(
    u1_struct_0('#skF_9') = k2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_131,c_96])).

tff(c_221,plain,(
    ! [A_100,B_101] :
      ( r1_xboole_0(u1_struct_0(A_100),u1_struct_0(B_101))
      | ~ r1_tsep_1(A_100,B_101)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_232,plain,(
    ! [B_101] :
      ( r1_xboole_0(k2_struct_0('#skF_9'),u1_struct_0(B_101))
      | ~ r1_tsep_1('#skF_9',B_101)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_221])).

tff(c_257,plain,(
    ! [B_102] :
      ( r1_xboole_0(k2_struct_0('#skF_9'),u1_struct_0(B_102))
      | ~ r1_tsep_1('#skF_9',B_102)
      | ~ l1_struct_0(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_232])).

tff(c_268,plain,
    ( r1_xboole_0(k2_struct_0('#skF_9'),k2_struct_0('#skF_10'))
    | ~ r1_tsep_1('#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_257])).

tff(c_276,plain,(
    r1_xboole_0(k2_struct_0('#skF_9'),k2_struct_0('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_97,c_268])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_318,plain,(
    ! [C_105] :
      ( ~ r2_hidden(C_105,k2_struct_0('#skF_10'))
      | ~ r2_hidden(C_105,k2_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_276,c_20])).

tff(c_328,plain,(
    ! [A_7] :
      ( ~ r2_hidden('#skF_3'(A_7,k2_struct_0('#skF_10')),k2_struct_0('#skF_9'))
      | r1_xboole_0(A_7,k2_struct_0('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_22,c_318])).

tff(c_4118,plain,(
    ! [B_310] :
      ( ~ m1_pre_topc(B_310,'#skF_9')
      | ~ l1_pre_topc(B_310)
      | ~ l1_pre_topc('#skF_9')
      | r1_xboole_0(k2_struct_0(B_310),k2_struct_0('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_4072,c_328])).

tff(c_4190,plain,(
    ! [B_316] :
      ( ~ m1_pre_topc(B_316,'#skF_9')
      | ~ l1_pre_topc(B_316)
      | r1_xboole_0(k2_struct_0(B_316),k2_struct_0('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_4118])).

tff(c_68,plain,
    ( ~ r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_tsep_1('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_98,plain,(
    ~ r1_tsep_1('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_143,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_127,c_96])).

tff(c_281,plain,(
    ! [A_103,B_104] :
      ( r1_tsep_1(A_103,B_104)
      | ~ r1_xboole_0(u1_struct_0(A_103),u1_struct_0(B_104))
      | ~ l1_struct_0(B_104)
      | ~ l1_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_302,plain,(
    ! [A_103] :
      ( r1_tsep_1(A_103,'#skF_10')
      | ~ r1_xboole_0(u1_struct_0(A_103),k2_struct_0('#skF_10'))
      | ~ l1_struct_0('#skF_10')
      | ~ l1_struct_0(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_281])).

tff(c_544,plain,(
    ! [A_121] :
      ( r1_tsep_1(A_121,'#skF_10')
      | ~ r1_xboole_0(u1_struct_0(A_121),k2_struct_0('#skF_10'))
      | ~ l1_struct_0(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_302])).

tff(c_550,plain,
    ( r1_tsep_1('#skF_8','#skF_10')
    | ~ r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_10'))
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_544])).

tff(c_561,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_10'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_550])).

tff(c_570,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_573,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_570])).

tff(c_577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_573])).

tff(c_578,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_4193,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_9')
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_4190,c_578])).

tff(c_4205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_4193])).

tff(c_4206,plain,(
    ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4207,plain,(
    r1_tsep_1('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4272,plain,(
    ! [B_335,A_336] :
      ( r1_tsep_1(B_335,A_336)
      | ~ r1_tsep_1(A_336,B_335)
      | ~ l1_struct_0(B_335)
      | ~ l1_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4274,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4207,c_4272])).

tff(c_4279,plain,
    ( ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_4206,c_4274])).

tff(c_4281,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4279])).

tff(c_4285,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_4281])).

tff(c_4289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_4285])).

tff(c_4290,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4279])).

tff(c_4299,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_4290])).

tff(c_4303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4233,c_4299])).

tff(c_4305,plain,(
    ~ r1_tsep_1('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4304,plain,(
    r1_tsep_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4371,plain,(
    ! [B_355,A_356] :
      ( r1_tsep_1(B_355,A_356)
      | ~ r1_tsep_1(A_356,B_355)
      | ~ l1_struct_0(B_355)
      | ~ l1_struct_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4373,plain,
    ( r1_tsep_1('#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4304,c_4371])).

tff(c_4376,plain,
    ( ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_4305,c_4373])).

tff(c_4377,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_4376])).

tff(c_4399,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_4377])).

tff(c_4403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4332,c_4399])).

tff(c_4404,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_4376])).

tff(c_4408,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_4404])).

tff(c_4412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4339,c_4408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.18  
% 6.00/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.19  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5
% 6.00/2.19  
% 6.00/2.19  %Foreground sorts:
% 6.00/2.19  
% 6.00/2.19  
% 6.00/2.19  %Background operators:
% 6.00/2.19  
% 6.00/2.19  
% 6.00/2.19  %Foreground operators:
% 6.00/2.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.00/2.19  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.00/2.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.00/2.19  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.00/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.00/2.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.00/2.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.00/2.19  tff('#skF_7', type, '#skF_7': $i).
% 6.00/2.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.00/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.19  tff('#skF_10', type, '#skF_10': $i).
% 6.00/2.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.00/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.00/2.19  tff('#skF_9', type, '#skF_9': $i).
% 6.00/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.00/2.19  tff('#skF_8', type, '#skF_8': $i).
% 6.00/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.00/2.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.00/2.19  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 6.00/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.00/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.00/2.19  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.00/2.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.00/2.19  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.00/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.19  
% 6.00/2.21  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 6.00/2.21  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.00/2.21  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.00/2.21  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.00/2.21  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 6.00/2.21  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.00/2.21  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.00/2.21  tff(f_109, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 6.00/2.21  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.00/2.21  tff(f_101, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 6.00/2.21  tff(c_86, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_78, plain, (m1_pre_topc('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_4317, plain, (![B_340, A_341]: (l1_pre_topc(B_340) | ~m1_pre_topc(B_340, A_341) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.00/2.21  tff(c_4329, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_78, c_4317])).
% 6.00/2.21  tff(c_4339, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4329])).
% 6.00/2.21  tff(c_58, plain, (![A_55]: (l1_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.00/2.21  tff(c_74, plain, (m1_pre_topc('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_4320, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_74, c_4317])).
% 6.00/2.21  tff(c_4332, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4320])).
% 6.00/2.21  tff(c_4218, plain, (![B_320, A_321]: (l1_pre_topc(B_320) | ~m1_pre_topc(B_320, A_321) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.00/2.21  tff(c_4221, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_74, c_4218])).
% 6.00/2.21  tff(c_4233, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4221])).
% 6.00/2.21  tff(c_82, plain, (m1_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_4224, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_4218])).
% 6.00/2.21  tff(c_4236, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4224])).
% 6.00/2.21  tff(c_109, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.00/2.21  tff(c_115, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_109])).
% 6.00/2.21  tff(c_127, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_115])).
% 6.00/2.21  tff(c_72, plain, (m1_pre_topc('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_121, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_78, c_109])).
% 6.00/2.21  tff(c_131, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_121])).
% 6.00/2.21  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.00/2.21  tff(c_368, plain, (![B_107, A_108]: (r1_tarski(k2_struct_0(B_107), k2_struct_0(A_108)) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(B_107) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.00/2.21  tff(c_26, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.00/2.21  tff(c_1586, plain, (![B_162, A_163]: (k2_xboole_0(k2_struct_0(B_162), k2_struct_0(A_163))=k2_struct_0(A_163) | ~m1_pre_topc(B_162, A_163) | ~l1_pre_topc(B_162) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_368, c_26])).
% 6.00/2.21  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.00/2.21  tff(c_1716, plain, (![D_171, B_172, A_173]: (~r2_hidden(D_171, k2_struct_0(B_172)) | r2_hidden(D_171, k2_struct_0(A_173)) | ~m1_pre_topc(B_172, A_173) | ~l1_pre_topc(B_172) | ~l1_pre_topc(A_173))), inference(superposition, [status(thm), theory('equality')], [c_1586, c_6])).
% 6.00/2.21  tff(c_4072, plain, (![B_310, B_311, A_312]: (r2_hidden('#skF_3'(k2_struct_0(B_310), B_311), k2_struct_0(A_312)) | ~m1_pre_topc(B_310, A_312) | ~l1_pre_topc(B_310) | ~l1_pre_topc(A_312) | r1_xboole_0(k2_struct_0(B_310), B_311))), inference(resolution, [status(thm)], [c_24, c_1716])).
% 6.00/2.21  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.00/2.21  tff(c_112, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_74, c_109])).
% 6.00/2.21  tff(c_124, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_112])).
% 6.00/2.21  tff(c_70, plain, (r1_tsep_1('#skF_10', '#skF_9') | r1_tsep_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_97, plain, (r1_tsep_1('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_70])).
% 6.00/2.21  tff(c_163, plain, (![B_95, A_96]: (r1_tsep_1(B_95, A_96) | ~r1_tsep_1(A_96, B_95) | ~l1_struct_0(B_95) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.00/2.21  tff(c_166, plain, (r1_tsep_1('#skF_10', '#skF_9') | ~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_97, c_163])).
% 6.00/2.21  tff(c_167, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_166])).
% 6.00/2.21  tff(c_170, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_58, c_167])).
% 6.00/2.21  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_170])).
% 6.00/2.21  tff(c_175, plain, (~l1_struct_0('#skF_10') | r1_tsep_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_166])).
% 6.00/2.21  tff(c_201, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_175])).
% 6.00/2.21  tff(c_204, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_58, c_201])).
% 6.00/2.21  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_204])).
% 6.00/2.21  tff(c_210, plain, (l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_175])).
% 6.00/2.21  tff(c_92, plain, (![A_76]: (u1_struct_0(A_76)=k2_struct_0(A_76) | ~l1_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.00/2.21  tff(c_96, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_58, c_92])).
% 6.00/2.21  tff(c_135, plain, (u1_struct_0('#skF_10')=k2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_124, c_96])).
% 6.00/2.21  tff(c_176, plain, (l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_166])).
% 6.00/2.21  tff(c_139, plain, (u1_struct_0('#skF_9')=k2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_131, c_96])).
% 6.00/2.21  tff(c_221, plain, (![A_100, B_101]: (r1_xboole_0(u1_struct_0(A_100), u1_struct_0(B_101)) | ~r1_tsep_1(A_100, B_101) | ~l1_struct_0(B_101) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.00/2.21  tff(c_232, plain, (![B_101]: (r1_xboole_0(k2_struct_0('#skF_9'), u1_struct_0(B_101)) | ~r1_tsep_1('#skF_9', B_101) | ~l1_struct_0(B_101) | ~l1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_221])).
% 6.00/2.21  tff(c_257, plain, (![B_102]: (r1_xboole_0(k2_struct_0('#skF_9'), u1_struct_0(B_102)) | ~r1_tsep_1('#skF_9', B_102) | ~l1_struct_0(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_232])).
% 6.00/2.21  tff(c_268, plain, (r1_xboole_0(k2_struct_0('#skF_9'), k2_struct_0('#skF_10')) | ~r1_tsep_1('#skF_9', '#skF_10') | ~l1_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_135, c_257])).
% 6.00/2.21  tff(c_276, plain, (r1_xboole_0(k2_struct_0('#skF_9'), k2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_97, c_268])).
% 6.00/2.21  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.00/2.21  tff(c_318, plain, (![C_105]: (~r2_hidden(C_105, k2_struct_0('#skF_10')) | ~r2_hidden(C_105, k2_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_276, c_20])).
% 6.00/2.21  tff(c_328, plain, (![A_7]: (~r2_hidden('#skF_3'(A_7, k2_struct_0('#skF_10')), k2_struct_0('#skF_9')) | r1_xboole_0(A_7, k2_struct_0('#skF_10')))), inference(resolution, [status(thm)], [c_22, c_318])).
% 6.00/2.21  tff(c_4118, plain, (![B_310]: (~m1_pre_topc(B_310, '#skF_9') | ~l1_pre_topc(B_310) | ~l1_pre_topc('#skF_9') | r1_xboole_0(k2_struct_0(B_310), k2_struct_0('#skF_10')))), inference(resolution, [status(thm)], [c_4072, c_328])).
% 6.00/2.21  tff(c_4190, plain, (![B_316]: (~m1_pre_topc(B_316, '#skF_9') | ~l1_pre_topc(B_316) | r1_xboole_0(k2_struct_0(B_316), k2_struct_0('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_4118])).
% 6.00/2.21  tff(c_68, plain, (~r1_tsep_1('#skF_10', '#skF_8') | ~r1_tsep_1('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.00/2.21  tff(c_98, plain, (~r1_tsep_1('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_68])).
% 6.00/2.21  tff(c_143, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_127, c_96])).
% 6.00/2.21  tff(c_281, plain, (![A_103, B_104]: (r1_tsep_1(A_103, B_104) | ~r1_xboole_0(u1_struct_0(A_103), u1_struct_0(B_104)) | ~l1_struct_0(B_104) | ~l1_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.00/2.21  tff(c_302, plain, (![A_103]: (r1_tsep_1(A_103, '#skF_10') | ~r1_xboole_0(u1_struct_0(A_103), k2_struct_0('#skF_10')) | ~l1_struct_0('#skF_10') | ~l1_struct_0(A_103))), inference(superposition, [status(thm), theory('equality')], [c_135, c_281])).
% 6.00/2.21  tff(c_544, plain, (![A_121]: (r1_tsep_1(A_121, '#skF_10') | ~r1_xboole_0(u1_struct_0(A_121), k2_struct_0('#skF_10')) | ~l1_struct_0(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_302])).
% 6.00/2.21  tff(c_550, plain, (r1_tsep_1('#skF_8', '#skF_10') | ~r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_10')) | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_143, c_544])).
% 6.00/2.21  tff(c_561, plain, (~r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_10')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_98, c_550])).
% 6.00/2.21  tff(c_570, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_561])).
% 6.00/2.21  tff(c_573, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_58, c_570])).
% 6.00/2.21  tff(c_577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_573])).
% 6.00/2.21  tff(c_578, plain, (~r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_10'))), inference(splitRight, [status(thm)], [c_561])).
% 6.00/2.21  tff(c_4193, plain, (~m1_pre_topc('#skF_8', '#skF_9') | ~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_4190, c_578])).
% 6.00/2.21  tff(c_4205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_4193])).
% 6.00/2.21  tff(c_4206, plain, (~r1_tsep_1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 6.00/2.21  tff(c_4207, plain, (r1_tsep_1('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_68])).
% 6.00/2.21  tff(c_4272, plain, (![B_335, A_336]: (r1_tsep_1(B_335, A_336) | ~r1_tsep_1(A_336, B_335) | ~l1_struct_0(B_335) | ~l1_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.00/2.21  tff(c_4274, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_4207, c_4272])).
% 6.00/2.21  tff(c_4279, plain, (~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4206, c_4274])).
% 6.00/2.21  tff(c_4281, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_4279])).
% 6.00/2.21  tff(c_4285, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_58, c_4281])).
% 6.00/2.21  tff(c_4289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4236, c_4285])).
% 6.00/2.21  tff(c_4290, plain, (~l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_4279])).
% 6.00/2.21  tff(c_4299, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_58, c_4290])).
% 6.00/2.21  tff(c_4303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4233, c_4299])).
% 6.00/2.21  tff(c_4305, plain, (~r1_tsep_1('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_70])).
% 6.00/2.21  tff(c_4304, plain, (r1_tsep_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 6.00/2.21  tff(c_4371, plain, (![B_355, A_356]: (r1_tsep_1(B_355, A_356) | ~r1_tsep_1(A_356, B_355) | ~l1_struct_0(B_355) | ~l1_struct_0(A_356))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.00/2.21  tff(c_4373, plain, (r1_tsep_1('#skF_9', '#skF_10') | ~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_4304, c_4371])).
% 6.00/2.21  tff(c_4376, plain, (~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_4305, c_4373])).
% 6.00/2.21  tff(c_4377, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_4376])).
% 6.00/2.21  tff(c_4399, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_58, c_4377])).
% 6.00/2.21  tff(c_4403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4332, c_4399])).
% 6.00/2.21  tff(c_4404, plain, (~l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_4376])).
% 6.00/2.21  tff(c_4408, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_58, c_4404])).
% 6.00/2.21  tff(c_4412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4339, c_4408])).
% 6.00/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.21  
% 6.00/2.21  Inference rules
% 6.00/2.21  ----------------------
% 6.00/2.21  #Ref     : 0
% 6.00/2.21  #Sup     : 849
% 6.00/2.21  #Fact    : 6
% 6.00/2.21  #Define  : 0
% 6.00/2.21  #Split   : 26
% 6.00/2.21  #Chain   : 0
% 6.00/2.21  #Close   : 0
% 6.00/2.21  
% 6.00/2.21  Ordering : KBO
% 6.00/2.21  
% 6.00/2.21  Simplification rules
% 6.00/2.21  ----------------------
% 6.00/2.21  #Subsume      : 245
% 6.00/2.21  #Demod        : 539
% 6.00/2.21  #Tautology    : 114
% 6.00/2.21  #SimpNegUnit  : 69
% 6.00/2.21  #BackRed      : 1
% 6.00/2.21  
% 6.00/2.21  #Partial instantiations: 0
% 6.00/2.21  #Strategies tried      : 1
% 6.00/2.21  
% 6.00/2.21  Timing (in seconds)
% 6.00/2.21  ----------------------
% 6.00/2.21  Preprocessing        : 0.35
% 6.00/2.21  Parsing              : 0.17
% 6.00/2.21  CNF conversion       : 0.03
% 6.00/2.21  Main loop            : 1.07
% 6.00/2.21  Inferencing          : 0.35
% 6.00/2.21  Reduction            : 0.31
% 6.00/2.21  Demodulation         : 0.20
% 6.00/2.21  BG Simplification    : 0.05
% 6.00/2.21  Subsumption          : 0.27
% 6.00/2.21  Abstraction          : 0.05
% 6.00/2.21  MUC search           : 0.00
% 6.00/2.21  Cooper               : 0.00
% 6.00/2.21  Total                : 1.48
% 6.00/2.21  Index Insertion      : 0.00
% 6.00/2.21  Index Deletion       : 0.00
% 6.00/2.21  Index Matching       : 0.00
% 6.00/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
