%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:08 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  158 (2530 expanded)
%              Number of leaves         :   44 ( 864 expanded)
%              Depth                    :   27
%              Number of atoms          :  349 (7422 expanded)
%              Number of equality atoms :   49 ( 915 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A,C)),u1_pre_topc(k1_tex_2(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_82,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_192,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(c_98,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_54,plain,(
    ! [A_53] :
      ( l1_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_105,plain,(
    ! [A_96] :
      ( u1_struct_0(A_96) = k2_struct_0(A_96)
      | ~ l1_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [A_98] :
      ( u1_struct_0(A_98) = k2_struct_0(A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_54,c_105])).

tff(c_115,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_111])).

tff(c_153,plain,(
    ! [A_106] :
      ( ~ v1_xboole_0(u1_struct_0(A_106))
      | ~ l1_struct_0(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_162,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_153])).

tff(c_165,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_162])).

tff(c_181,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_184,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_181])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_184])).

tff(c_189,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_92,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_131,plain,(
    ! [B_104,A_105] :
      ( l1_pre_topc(B_104)
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_137,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_131])).

tff(c_141,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_137])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_109,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_54,c_105])).

tff(c_145,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_141,c_109])).

tff(c_156,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_153])).

tff(c_163,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_156])).

tff(c_166,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_169,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_169])).

tff(c_174,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_175,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_94,plain,(
    v7_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_240,plain,(
    ! [A_123] :
      ( m1_subset_1('#skF_5'(A_123),u1_struct_0(A_123))
      | ~ v7_struct_0(A_123)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_249,plain,
    ( m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_7'))
    | ~ v7_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_240])).

tff(c_256,plain,
    ( m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_94,c_249])).

tff(c_257,plain,(
    m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_256])).

tff(c_431,plain,(
    ! [B_145,A_146] :
      ( r1_tarski(k2_struct_0(B_145),k2_struct_0(A_146))
      | ~ m1_pre_topc(B_145,A_146)
      | ~ l1_pre_topc(B_145)
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_228,plain,(
    ! [C_118,B_119,A_120] :
      ( r2_hidden(C_118,B_119)
      | ~ r2_hidden(C_118,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_234,plain,(
    ! [A_10,B_119,B_11] :
      ( r2_hidden(A_10,B_119)
      | ~ r1_tarski(B_11,B_119)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_1417,plain,(
    ! [A_236,A_237,B_238] :
      ( r2_hidden(A_236,k2_struct_0(A_237))
      | v1_xboole_0(k2_struct_0(B_238))
      | ~ m1_subset_1(A_236,k2_struct_0(B_238))
      | ~ m1_pre_topc(B_238,A_237)
      | ~ l1_pre_topc(B_238)
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_431,c_234])).

tff(c_1425,plain,(
    ! [A_237] :
      ( r2_hidden('#skF_5'('#skF_7'),k2_struct_0(A_237))
      | v1_xboole_0(k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_237)
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_257,c_1417])).

tff(c_1433,plain,(
    ! [A_237] :
      ( r2_hidden('#skF_5'('#skF_7'),k2_struct_0(A_237))
      | v1_xboole_0(k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1425])).

tff(c_1451,plain,(
    ! [A_241] :
      ( r2_hidden('#skF_5'('#skF_7'),k2_struct_0(A_241))
      | ~ m1_pre_topc('#skF_7',A_241)
      | ~ l1_pre_topc(A_241) ) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_1433])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1467,plain,(
    ! [A_244] :
      ( m1_subset_1('#skF_5'('#skF_7'),k2_struct_0(A_244))
      | v1_xboole_0(k2_struct_0(A_244))
      | ~ m1_pre_topc('#skF_7',A_244)
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_1451,c_14])).

tff(c_467,plain,(
    ! [A_152,B_153] :
      ( m1_pre_topc(k1_tex_2(A_152,B_153),A_152)
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_479,plain,(
    ! [B_153] :
      ( m1_pre_topc(k1_tex_2('#skF_6',B_153),'#skF_6')
      | ~ m1_subset_1(B_153,k2_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_467])).

tff(c_487,plain,(
    ! [B_153] :
      ( m1_pre_topc(k1_tex_2('#skF_6',B_153),'#skF_6')
      | ~ m1_subset_1(B_153,k2_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_479])).

tff(c_488,plain,(
    ! [B_153] :
      ( m1_pre_topc(k1_tex_2('#skF_6',B_153),'#skF_6')
      | ~ m1_subset_1(B_153,k2_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_487])).

tff(c_1489,plain,
    ( m1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')),'#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1467,c_488])).

tff(c_1535,plain,
    ( m1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')),'#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92,c_1489])).

tff(c_1536,plain,(
    m1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1535])).

tff(c_56,plain,(
    ! [B_56,A_54] :
      ( l1_pre_topc(B_56)
      | ~ m1_pre_topc(B_56,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1566,plain,
    ( l1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1536,c_56])).

tff(c_1575,plain,(
    l1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1566])).

tff(c_1579,plain,(
    u1_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) = k2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1575,c_109])).

tff(c_973,plain,(
    ! [C_201,B_202,A_203] :
      ( g1_pre_topc(u1_struct_0(C_201),u1_pre_topc(C_201)) = g1_pre_topc(u1_struct_0(B_202),u1_pre_topc(B_202))
      | u1_struct_0(C_201) != u1_struct_0(B_202)
      | ~ m1_pre_topc(C_201,A_203)
      | ~ m1_pre_topc(B_202,A_203)
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_995,plain,(
    ! [B_202] :
      ( g1_pre_topc(u1_struct_0(B_202),u1_pre_topc(B_202)) = g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
      | u1_struct_0(B_202) != u1_struct_0('#skF_7')
      | ~ m1_pre_topc(B_202,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_92,c_973])).

tff(c_1041,plain,(
    ! [B_212] :
      ( g1_pre_topc(u1_struct_0(B_212),u1_pre_topc(B_212)) = g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
      | u1_struct_0(B_212) != k2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_212,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_145,c_145,c_995])).

tff(c_90,plain,(
    ! [C_92] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_6',C_92)),u1_pre_topc(k1_tex_2('#skF_6',C_92))) != g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(C_92,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_116,plain,(
    ! [C_92] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_6',C_92)),u1_pre_topc(k1_tex_2('#skF_6',C_92))) != g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_90])).

tff(c_204,plain,(
    ! [C_92] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_6',C_92)),u1_pre_topc(k1_tex_2('#skF_6',C_92))) != g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(C_92,k2_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_116])).

tff(c_1067,plain,(
    ! [C_92] :
      ( ~ m1_subset_1(C_92,k2_struct_0('#skF_6'))
      | u1_struct_0(k1_tex_2('#skF_6',C_92)) != k2_struct_0('#skF_7')
      | ~ m1_pre_topc(k1_tex_2('#skF_6',C_92),'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_204])).

tff(c_1473,plain,
    ( u1_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) != k2_struct_0('#skF_7')
    | ~ m1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')),'#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1467,c_1067])).

tff(c_1519,plain,
    ( u1_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) != k2_struct_0('#skF_7')
    | ~ m1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')),'#skF_6')
    | v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92,c_1473])).

tff(c_1520,plain,
    ( u1_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) != k2_struct_0('#skF_7')
    | ~ m1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1519])).

tff(c_1727,plain,(
    k2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) != k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_1579,c_1520])).

tff(c_68,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_263,plain,
    ( k6_domain_1(k2_struct_0('#skF_7'),'#skF_5'('#skF_7')) = k1_tarski('#skF_5'('#skF_7'))
    | v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_257,c_68])).

tff(c_269,plain,(
    k6_domain_1(k2_struct_0('#skF_7'),'#skF_5'('#skF_7')) = k1_tarski('#skF_5'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_263])).

tff(c_529,plain,(
    ! [A_156] :
      ( k6_domain_1(u1_struct_0(A_156),'#skF_5'(A_156)) = u1_struct_0(A_156)
      | ~ v7_struct_0(A_156)
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_538,plain,
    ( k6_domain_1(k2_struct_0('#skF_7'),'#skF_5'('#skF_7')) = u1_struct_0('#skF_7')
    | ~ v7_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_529])).

tff(c_545,plain,
    ( k1_tarski('#skF_5'('#skF_7')) = k2_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_94,c_269,c_145,c_538])).

tff(c_546,plain,(
    k1_tarski('#skF_5'('#skF_7')) = k2_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_545])).

tff(c_70,plain,(
    ! [A_67] :
      ( m1_pre_topc(A_67,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1065,plain,
    ( g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | u1_struct_0('#skF_6') != k2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1041])).

tff(c_1073,plain,
    ( g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | k2_struct_0('#skF_7') != k2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1065])).

tff(c_1338,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1073])).

tff(c_1341,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1338])).

tff(c_1345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1341])).

tff(c_1347,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1073])).

tff(c_44,plain,(
    ! [B_35,A_13] :
      ( r1_tarski(k2_struct_0(B_35),k2_struct_0(A_13))
      | ~ m1_pre_topc(B_35,A_13)
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1459,plain,(
    ! [B_242,A_243] :
      ( r2_hidden('#skF_5'('#skF_7'),B_242)
      | ~ r1_tarski(k2_struct_0(A_243),B_242)
      | ~ m1_pre_topc('#skF_7',A_243)
      | ~ l1_pre_topc(A_243) ) ),
    inference(resolution,[status(thm)],[c_1451,c_2])).

tff(c_1826,plain,(
    ! [A_252,B_253] :
      ( r2_hidden('#skF_5'('#skF_7'),k2_struct_0(A_252))
      | ~ m1_pre_topc('#skF_7',B_253)
      | ~ m1_pre_topc(B_253,A_252)
      | ~ l1_pre_topc(B_253)
      | ~ l1_pre_topc(A_252) ) ),
    inference(resolution,[status(thm)],[c_44,c_1459])).

tff(c_1840,plain,(
    ! [A_252] :
      ( r2_hidden('#skF_5'('#skF_7'),k2_struct_0(A_252))
      | ~ m1_pre_topc('#skF_6',A_252)
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_252) ) ),
    inference(resolution,[status(thm)],[c_92,c_1826])).

tff(c_1856,plain,(
    ! [A_254] :
      ( r2_hidden('#skF_5'('#skF_7'),k2_struct_0(A_254))
      | ~ m1_pre_topc('#skF_6',A_254)
      | ~ l1_pre_topc(A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1840])).

tff(c_1863,plain,(
    ! [A_254] :
      ( m1_subset_1('#skF_5'('#skF_7'),k2_struct_0(A_254))
      | v1_xboole_0(k2_struct_0(A_254))
      | ~ m1_pre_topc('#skF_6',A_254)
      | ~ l1_pre_topc(A_254) ) ),
    inference(resolution,[status(thm)],[c_1856,c_14])).

tff(c_314,plain,(
    ! [A_134,B_135] :
      ( ~ v2_struct_0(k1_tex_2(A_134,B_135))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_331,plain,(
    ! [B_135] :
      ( ~ v2_struct_0(k1_tex_2('#skF_6',B_135))
      | ~ m1_subset_1(B_135,k2_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_314])).

tff(c_339,plain,(
    ! [B_135] :
      ( ~ v2_struct_0(k1_tex_2('#skF_6',B_135))
      | ~ m1_subset_1(B_135,k2_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_331])).

tff(c_340,plain,(
    ! [B_135] :
      ( ~ v2_struct_0(k1_tex_2('#skF_6',B_135))
      | ~ m1_subset_1(B_135,k2_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_339])).

tff(c_1497,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1467,c_340])).

tff(c_1543,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92,c_1497])).

tff(c_1544,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1543])).

tff(c_341,plain,(
    ! [A_136,B_137] :
      ( v1_pre_topc(k1_tex_2(A_136,B_137))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_358,plain,(
    ! [B_137] :
      ( v1_pre_topc(k1_tex_2('#skF_6',B_137))
      | ~ m1_subset_1(B_137,k2_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_341])).

tff(c_366,plain,(
    ! [B_137] :
      ( v1_pre_topc(k1_tex_2('#skF_6',B_137))
      | ~ m1_subset_1(B_137,k2_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_358])).

tff(c_367,plain,(
    ! [B_137] :
      ( v1_pre_topc(k1_tex_2('#skF_6',B_137))
      | ~ m1_subset_1(B_137,k2_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_366])).

tff(c_1501,plain,
    ( v1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1467,c_367])).

tff(c_1547,plain,
    ( v1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_92,c_1501])).

tff(c_1548,plain,(
    v1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1547])).

tff(c_2172,plain,(
    ! [A_269,B_270] :
      ( k6_domain_1(u1_struct_0(A_269),B_270) = u1_struct_0(k1_tex_2(A_269,B_270))
      | ~ m1_pre_topc(k1_tex_2(A_269,B_270),A_269)
      | ~ v1_pre_topc(k1_tex_2(A_269,B_270))
      | v2_struct_0(k1_tex_2(A_269,B_270))
      | ~ m1_subset_1(B_270,u1_struct_0(A_269))
      | ~ l1_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2174,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_5'('#skF_7')) = u1_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | ~ v1_pre_topc(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | v2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | ~ m1_subset_1('#skF_5'('#skF_7'),u1_struct_0('#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1536,c_2172])).

tff(c_2200,plain,
    ( k6_domain_1(k2_struct_0('#skF_6'),'#skF_5'('#skF_7')) = k2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | v2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | ~ m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_115,c_1548,c_115,c_1579,c_2174])).

tff(c_2201,plain,
    ( k6_domain_1(k2_struct_0('#skF_6'),'#skF_5'('#skF_7')) = k2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7')))
    | ~ m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1544,c_2200])).

tff(c_2439,plain,(
    ~ m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2201])).

tff(c_2442,plain,
    ( v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1863,c_2439])).

tff(c_2451,plain,(
    v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1347,c_2442])).

tff(c_2453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_2451])).

tff(c_2455,plain,(
    m1_subset_1('#skF_5'('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2201])).

tff(c_2475,plain,
    ( k6_domain_1(k2_struct_0('#skF_6'),'#skF_5'('#skF_7')) = k1_tarski('#skF_5'('#skF_7'))
    | v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2455,c_68])).

tff(c_2493,plain,
    ( k6_domain_1(k2_struct_0('#skF_6'),'#skF_5'('#skF_7')) = k2_struct_0('#skF_7')
    | v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_2475])).

tff(c_2494,plain,(
    k6_domain_1(k2_struct_0('#skF_6'),'#skF_5'('#skF_7')) = k2_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_2493])).

tff(c_2454,plain,(
    k6_domain_1(k2_struct_0('#skF_6'),'#skF_5'('#skF_7')) = k2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_2201])).

tff(c_2533,plain,(
    k2_struct_0(k1_tex_2('#skF_6','#skF_5'('#skF_7'))) = k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_2454])).

tff(c_2534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1727,c_2533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.87  
% 4.82/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.87  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.82/1.87  
% 4.82/1.87  %Foreground sorts:
% 4.82/1.87  
% 4.82/1.87  
% 4.82/1.87  %Background operators:
% 4.82/1.87  
% 4.82/1.87  
% 4.82/1.87  %Foreground operators:
% 4.82/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.82/1.87  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.82/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.82/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.82/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.87  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.82/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.82/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.82/1.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.82/1.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.82/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.82/1.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.82/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.82/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.87  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 4.82/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.82/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.82/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.82/1.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.82/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.82/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.82/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.87  
% 4.82/1.89  tff(f_211, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v7_struct_0(B)) & m1_pre_topc(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A, C)), u1_pre_topc(k1_tex_2(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tex_2)).
% 4.82/1.89  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.82/1.89  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.82/1.89  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.82/1.89  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.82/1.89  tff(f_158, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (v7_struct_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (u1_struct_0(A) = k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 4.82/1.89  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 4.82/1.89  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.82/1.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.82/1.89  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.82/1.89  tff(f_192, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 4.82/1.89  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => ((u1_struct_0(B) = u1_struct_0(C)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tsep_1)).
% 4.82/1.89  tff(f_130, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.82/1.89  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.82/1.89  tff(f_178, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 4.82/1.89  tff(c_98, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.82/1.89  tff(c_54, plain, (![A_53]: (l1_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.89  tff(c_100, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.82/1.89  tff(c_105, plain, (![A_96]: (u1_struct_0(A_96)=k2_struct_0(A_96) | ~l1_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.82/1.89  tff(c_111, plain, (![A_98]: (u1_struct_0(A_98)=k2_struct_0(A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_54, c_105])).
% 4.82/1.89  tff(c_115, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_98, c_111])).
% 4.82/1.89  tff(c_153, plain, (![A_106]: (~v1_xboole_0(u1_struct_0(A_106)) | ~l1_struct_0(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.82/1.89  tff(c_162, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_115, c_153])).
% 4.82/1.89  tff(c_165, plain, (~v1_xboole_0(k2_struct_0('#skF_6')) | ~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_100, c_162])).
% 4.82/1.89  tff(c_181, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_165])).
% 4.82/1.89  tff(c_184, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_54, c_181])).
% 4.82/1.89  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_184])).
% 4.82/1.89  tff(c_189, plain, (~v1_xboole_0(k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_165])).
% 4.82/1.89  tff(c_92, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.82/1.89  tff(c_131, plain, (![B_104, A_105]: (l1_pre_topc(B_104) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.82/1.89  tff(c_137, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_92, c_131])).
% 4.82/1.89  tff(c_141, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_137])).
% 4.82/1.89  tff(c_96, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.82/1.89  tff(c_109, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_54, c_105])).
% 4.82/1.89  tff(c_145, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_141, c_109])).
% 4.82/1.89  tff(c_156, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_145, c_153])).
% 4.82/1.89  tff(c_163, plain, (~v1_xboole_0(k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_96, c_156])).
% 4.82/1.89  tff(c_166, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_163])).
% 4.82/1.89  tff(c_169, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_54, c_166])).
% 4.82/1.89  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_169])).
% 4.82/1.89  tff(c_174, plain, (~v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_163])).
% 4.82/1.89  tff(c_175, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_163])).
% 4.82/1.89  tff(c_94, plain, (v7_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.82/1.89  tff(c_240, plain, (![A_123]: (m1_subset_1('#skF_5'(A_123), u1_struct_0(A_123)) | ~v7_struct_0(A_123) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.82/1.89  tff(c_249, plain, (m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_7')) | ~v7_struct_0('#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_145, c_240])).
% 4.82/1.89  tff(c_256, plain, (m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_94, c_249])).
% 4.82/1.89  tff(c_257, plain, (m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_96, c_256])).
% 4.82/1.89  tff(c_431, plain, (![B_145, A_146]: (r1_tarski(k2_struct_0(B_145), k2_struct_0(A_146)) | ~m1_pre_topc(B_145, A_146) | ~l1_pre_topc(B_145) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.82/1.89  tff(c_22, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.82/1.89  tff(c_228, plain, (![C_118, B_119, A_120]: (r2_hidden(C_118, B_119) | ~r2_hidden(C_118, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.82/1.89  tff(c_234, plain, (![A_10, B_119, B_11]: (r2_hidden(A_10, B_119) | ~r1_tarski(B_11, B_119) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(resolution, [status(thm)], [c_22, c_228])).
% 4.82/1.89  tff(c_1417, plain, (![A_236, A_237, B_238]: (r2_hidden(A_236, k2_struct_0(A_237)) | v1_xboole_0(k2_struct_0(B_238)) | ~m1_subset_1(A_236, k2_struct_0(B_238)) | ~m1_pre_topc(B_238, A_237) | ~l1_pre_topc(B_238) | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_431, c_234])).
% 4.82/1.89  tff(c_1425, plain, (![A_237]: (r2_hidden('#skF_5'('#skF_7'), k2_struct_0(A_237)) | v1_xboole_0(k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_237) | ~l1_pre_topc('#skF_7') | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_257, c_1417])).
% 4.82/1.89  tff(c_1433, plain, (![A_237]: (r2_hidden('#skF_5'('#skF_7'), k2_struct_0(A_237)) | v1_xboole_0(k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_237) | ~l1_pre_topc(A_237))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1425])).
% 4.82/1.89  tff(c_1451, plain, (![A_241]: (r2_hidden('#skF_5'('#skF_7'), k2_struct_0(A_241)) | ~m1_pre_topc('#skF_7', A_241) | ~l1_pre_topc(A_241))), inference(negUnitSimplification, [status(thm)], [c_174, c_1433])).
% 4.82/1.89  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.82/1.89  tff(c_1467, plain, (![A_244]: (m1_subset_1('#skF_5'('#skF_7'), k2_struct_0(A_244)) | v1_xboole_0(k2_struct_0(A_244)) | ~m1_pre_topc('#skF_7', A_244) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_1451, c_14])).
% 4.82/1.89  tff(c_467, plain, (![A_152, B_153]: (m1_pre_topc(k1_tex_2(A_152, B_153), A_152) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.82/1.89  tff(c_479, plain, (![B_153]: (m1_pre_topc(k1_tex_2('#skF_6', B_153), '#skF_6') | ~m1_subset_1(B_153, k2_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_467])).
% 4.82/1.89  tff(c_487, plain, (![B_153]: (m1_pre_topc(k1_tex_2('#skF_6', B_153), '#skF_6') | ~m1_subset_1(B_153, k2_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_479])).
% 4.82/1.89  tff(c_488, plain, (![B_153]: (m1_pre_topc(k1_tex_2('#skF_6', B_153), '#skF_6') | ~m1_subset_1(B_153, k2_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_100, c_487])).
% 4.82/1.89  tff(c_1489, plain, (m1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')), '#skF_6') | v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1467, c_488])).
% 4.82/1.89  tff(c_1535, plain, (m1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')), '#skF_6') | v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92, c_1489])).
% 4.82/1.89  tff(c_1536, plain, (m1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_189, c_1535])).
% 4.82/1.89  tff(c_56, plain, (![B_56, A_54]: (l1_pre_topc(B_56) | ~m1_pre_topc(B_56, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.82/1.89  tff(c_1566, plain, (l1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1536, c_56])).
% 4.82/1.89  tff(c_1575, plain, (l1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1566])).
% 4.82/1.89  tff(c_1579, plain, (u1_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))=k2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))), inference(resolution, [status(thm)], [c_1575, c_109])).
% 4.82/1.89  tff(c_973, plain, (![C_201, B_202, A_203]: (g1_pre_topc(u1_struct_0(C_201), u1_pre_topc(C_201))=g1_pre_topc(u1_struct_0(B_202), u1_pre_topc(B_202)) | u1_struct_0(C_201)!=u1_struct_0(B_202) | ~m1_pre_topc(C_201, A_203) | ~m1_pre_topc(B_202, A_203) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.82/1.89  tff(c_995, plain, (![B_202]: (g1_pre_topc(u1_struct_0(B_202), u1_pre_topc(B_202))=g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | u1_struct_0(B_202)!=u1_struct_0('#skF_7') | ~m1_pre_topc(B_202, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_92, c_973])).
% 4.82/1.89  tff(c_1041, plain, (![B_212]: (g1_pre_topc(u1_struct_0(B_212), u1_pre_topc(B_212))=g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | u1_struct_0(B_212)!=k2_struct_0('#skF_7') | ~m1_pre_topc(B_212, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_145, c_145, c_995])).
% 4.82/1.89  tff(c_90, plain, (![C_92]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_6', C_92)), u1_pre_topc(k1_tex_2('#skF_6', C_92)))!=g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | ~m1_subset_1(C_92, u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.82/1.89  tff(c_116, plain, (![C_92]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_6', C_92)), u1_pre_topc(k1_tex_2('#skF_6', C_92)))!=g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | ~m1_subset_1(C_92, k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_90])).
% 4.82/1.89  tff(c_204, plain, (![C_92]: (g1_pre_topc(u1_struct_0(k1_tex_2('#skF_6', C_92)), u1_pre_topc(k1_tex_2('#skF_6', C_92)))!=g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | ~m1_subset_1(C_92, k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_116])).
% 4.82/1.89  tff(c_1067, plain, (![C_92]: (~m1_subset_1(C_92, k2_struct_0('#skF_6')) | u1_struct_0(k1_tex_2('#skF_6', C_92))!=k2_struct_0('#skF_7') | ~m1_pre_topc(k1_tex_2('#skF_6', C_92), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_204])).
% 4.82/1.89  tff(c_1473, plain, (u1_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))!=k2_struct_0('#skF_7') | ~m1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')), '#skF_6') | v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1467, c_1067])).
% 4.82/1.89  tff(c_1519, plain, (u1_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))!=k2_struct_0('#skF_7') | ~m1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')), '#skF_6') | v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92, c_1473])).
% 4.82/1.89  tff(c_1520, plain, (u1_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))!=k2_struct_0('#skF_7') | ~m1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_189, c_1519])).
% 4.82/1.89  tff(c_1727, plain, (k2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))!=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_1579, c_1520])).
% 4.82/1.89  tff(c_68, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.82/1.89  tff(c_263, plain, (k6_domain_1(k2_struct_0('#skF_7'), '#skF_5'('#skF_7'))=k1_tarski('#skF_5'('#skF_7')) | v1_xboole_0(k2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_257, c_68])).
% 4.82/1.89  tff(c_269, plain, (k6_domain_1(k2_struct_0('#skF_7'), '#skF_5'('#skF_7'))=k1_tarski('#skF_5'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_174, c_263])).
% 4.82/1.89  tff(c_529, plain, (![A_156]: (k6_domain_1(u1_struct_0(A_156), '#skF_5'(A_156))=u1_struct_0(A_156) | ~v7_struct_0(A_156) | ~l1_struct_0(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.82/1.89  tff(c_538, plain, (k6_domain_1(k2_struct_0('#skF_7'), '#skF_5'('#skF_7'))=u1_struct_0('#skF_7') | ~v7_struct_0('#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_145, c_529])).
% 4.82/1.89  tff(c_545, plain, (k1_tarski('#skF_5'('#skF_7'))=k2_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_94, c_269, c_145, c_538])).
% 4.82/1.89  tff(c_546, plain, (k1_tarski('#skF_5'('#skF_7'))=k2_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_96, c_545])).
% 4.82/1.89  tff(c_70, plain, (![A_67]: (m1_pre_topc(A_67, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.82/1.89  tff(c_1065, plain, (g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7'))=g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | u1_struct_0('#skF_6')!=k2_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_115, c_1041])).
% 4.82/1.89  tff(c_1073, plain, (g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7'))=g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | k2_struct_0('#skF_7')!=k2_struct_0('#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_1065])).
% 4.82/1.89  tff(c_1338, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_1073])).
% 4.82/1.89  tff(c_1341, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_1338])).
% 4.82/1.89  tff(c_1345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_1341])).
% 4.82/1.89  tff(c_1347, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_1073])).
% 4.82/1.89  tff(c_44, plain, (![B_35, A_13]: (r1_tarski(k2_struct_0(B_35), k2_struct_0(A_13)) | ~m1_pre_topc(B_35, A_13) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.82/1.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.82/1.89  tff(c_1459, plain, (![B_242, A_243]: (r2_hidden('#skF_5'('#skF_7'), B_242) | ~r1_tarski(k2_struct_0(A_243), B_242) | ~m1_pre_topc('#skF_7', A_243) | ~l1_pre_topc(A_243))), inference(resolution, [status(thm)], [c_1451, c_2])).
% 4.82/1.89  tff(c_1826, plain, (![A_252, B_253]: (r2_hidden('#skF_5'('#skF_7'), k2_struct_0(A_252)) | ~m1_pre_topc('#skF_7', B_253) | ~m1_pre_topc(B_253, A_252) | ~l1_pre_topc(B_253) | ~l1_pre_topc(A_252))), inference(resolution, [status(thm)], [c_44, c_1459])).
% 4.82/1.89  tff(c_1840, plain, (![A_252]: (r2_hidden('#skF_5'('#skF_7'), k2_struct_0(A_252)) | ~m1_pre_topc('#skF_6', A_252) | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_252))), inference(resolution, [status(thm)], [c_92, c_1826])).
% 4.82/1.89  tff(c_1856, plain, (![A_254]: (r2_hidden('#skF_5'('#skF_7'), k2_struct_0(A_254)) | ~m1_pre_topc('#skF_6', A_254) | ~l1_pre_topc(A_254))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1840])).
% 4.82/1.89  tff(c_1863, plain, (![A_254]: (m1_subset_1('#skF_5'('#skF_7'), k2_struct_0(A_254)) | v1_xboole_0(k2_struct_0(A_254)) | ~m1_pre_topc('#skF_6', A_254) | ~l1_pre_topc(A_254))), inference(resolution, [status(thm)], [c_1856, c_14])).
% 4.82/1.89  tff(c_314, plain, (![A_134, B_135]: (~v2_struct_0(k1_tex_2(A_134, B_135)) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.82/1.89  tff(c_331, plain, (![B_135]: (~v2_struct_0(k1_tex_2('#skF_6', B_135)) | ~m1_subset_1(B_135, k2_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_314])).
% 4.82/1.89  tff(c_339, plain, (![B_135]: (~v2_struct_0(k1_tex_2('#skF_6', B_135)) | ~m1_subset_1(B_135, k2_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_331])).
% 4.82/1.89  tff(c_340, plain, (![B_135]: (~v2_struct_0(k1_tex_2('#skF_6', B_135)) | ~m1_subset_1(B_135, k2_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_100, c_339])).
% 4.82/1.89  tff(c_1497, plain, (~v2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1467, c_340])).
% 4.82/1.89  tff(c_1543, plain, (~v2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92, c_1497])).
% 4.82/1.89  tff(c_1544, plain, (~v2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_189, c_1543])).
% 4.82/1.89  tff(c_341, plain, (![A_136, B_137]: (v1_pre_topc(k1_tex_2(A_136, B_137)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.82/1.89  tff(c_358, plain, (![B_137]: (v1_pre_topc(k1_tex_2('#skF_6', B_137)) | ~m1_subset_1(B_137, k2_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_341])).
% 4.82/1.89  tff(c_366, plain, (![B_137]: (v1_pre_topc(k1_tex_2('#skF_6', B_137)) | ~m1_subset_1(B_137, k2_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_358])).
% 4.82/1.89  tff(c_367, plain, (![B_137]: (v1_pre_topc(k1_tex_2('#skF_6', B_137)) | ~m1_subset_1(B_137, k2_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_100, c_366])).
% 4.82/1.89  tff(c_1501, plain, (v1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1467, c_367])).
% 4.82/1.89  tff(c_1547, plain, (v1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_92, c_1501])).
% 4.82/1.89  tff(c_1548, plain, (v1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_189, c_1547])).
% 4.82/1.89  tff(c_2172, plain, (![A_269, B_270]: (k6_domain_1(u1_struct_0(A_269), B_270)=u1_struct_0(k1_tex_2(A_269, B_270)) | ~m1_pre_topc(k1_tex_2(A_269, B_270), A_269) | ~v1_pre_topc(k1_tex_2(A_269, B_270)) | v2_struct_0(k1_tex_2(A_269, B_270)) | ~m1_subset_1(B_270, u1_struct_0(A_269)) | ~l1_pre_topc(A_269) | v2_struct_0(A_269))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.82/1.89  tff(c_2174, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_5'('#skF_7'))=u1_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | ~v1_pre_topc(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | v2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | ~m1_subset_1('#skF_5'('#skF_7'), u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1536, c_2172])).
% 4.82/1.89  tff(c_2200, plain, (k6_domain_1(k2_struct_0('#skF_6'), '#skF_5'('#skF_7'))=k2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | v2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | ~m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_115, c_1548, c_115, c_1579, c_2174])).
% 4.82/1.89  tff(c_2201, plain, (k6_domain_1(k2_struct_0('#skF_6'), '#skF_5'('#skF_7'))=k2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7'))) | ~m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_100, c_1544, c_2200])).
% 4.82/1.89  tff(c_2439, plain, (~m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_2201])).
% 4.82/1.89  tff(c_2442, plain, (v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1863, c_2439])).
% 4.82/1.89  tff(c_2451, plain, (v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1347, c_2442])).
% 4.82/1.89  tff(c_2453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_2451])).
% 4.82/1.89  tff(c_2455, plain, (m1_subset_1('#skF_5'('#skF_7'), k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_2201])).
% 4.82/1.89  tff(c_2475, plain, (k6_domain_1(k2_struct_0('#skF_6'), '#skF_5'('#skF_7'))=k1_tarski('#skF_5'('#skF_7')) | v1_xboole_0(k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2455, c_68])).
% 4.82/1.89  tff(c_2493, plain, (k6_domain_1(k2_struct_0('#skF_6'), '#skF_5'('#skF_7'))=k2_struct_0('#skF_7') | v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_2475])).
% 4.82/1.89  tff(c_2494, plain, (k6_domain_1(k2_struct_0('#skF_6'), '#skF_5'('#skF_7'))=k2_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_189, c_2493])).
% 4.82/1.89  tff(c_2454, plain, (k6_domain_1(k2_struct_0('#skF_6'), '#skF_5'('#skF_7'))=k2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))), inference(splitRight, [status(thm)], [c_2201])).
% 4.82/1.89  tff(c_2533, plain, (k2_struct_0(k1_tex_2('#skF_6', '#skF_5'('#skF_7')))=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_2454])).
% 4.82/1.89  tff(c_2534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1727, c_2533])).
% 4.82/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.89  
% 4.82/1.89  Inference rules
% 4.82/1.89  ----------------------
% 4.82/1.89  #Ref     : 0
% 4.82/1.89  #Sup     : 470
% 4.82/1.89  #Fact    : 0
% 4.82/1.89  #Define  : 0
% 4.82/1.89  #Split   : 15
% 4.82/1.89  #Chain   : 0
% 4.82/1.89  #Close   : 0
% 4.82/1.89  
% 4.82/1.89  Ordering : KBO
% 4.82/1.89  
% 4.82/1.89  Simplification rules
% 4.82/1.89  ----------------------
% 4.82/1.89  #Subsume      : 97
% 4.82/1.89  #Demod        : 355
% 4.82/1.89  #Tautology    : 93
% 4.82/1.89  #SimpNegUnit  : 152
% 4.82/1.89  #BackRed      : 7
% 4.82/1.89  
% 4.82/1.89  #Partial instantiations: 0
% 4.82/1.89  #Strategies tried      : 1
% 4.82/1.89  
% 4.82/1.89  Timing (in seconds)
% 4.82/1.89  ----------------------
% 4.82/1.89  Preprocessing        : 0.40
% 4.82/1.90  Parsing              : 0.20
% 4.82/1.90  CNF conversion       : 0.03
% 4.82/1.90  Main loop            : 0.71
% 4.82/1.90  Inferencing          : 0.23
% 4.82/1.90  Reduction            : 0.24
% 4.82/1.90  Demodulation         : 0.16
% 4.82/1.90  BG Simplification    : 0.04
% 4.82/1.90  Subsumption          : 0.15
% 4.82/1.90  Abstraction          : 0.04
% 4.82/1.90  MUC search           : 0.00
% 4.82/1.90  Cooper               : 0.00
% 4.82/1.90  Total                : 1.15
% 4.82/1.90  Index Insertion      : 0.00
% 4.82/1.90  Index Deletion       : 0.00
% 4.82/1.90  Index Matching       : 0.00
% 4.82/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
