%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 163 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  141 ( 445 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_28,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_108,plain,(
    ! [B_58,A_59] :
      ( m1_subset_1(B_58,A_59)
      | ~ r2_hidden(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,
    ( m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_108])).

tff(c_126,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_120])).

tff(c_225,plain,(
    ! [A_76,B_77] :
      ( k6_domain_1(A_76,B_77) = k1_tarski(B_77)
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_231,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_225])).

tff(c_244,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_231])).

tff(c_344,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k6_domain_1(A_87,B_88),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_362,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_344])).

tff(c_372,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_362])).

tff(c_373,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_372])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_252,plain,(
    ! [C_78,A_79,B_80] :
      ( r2_hidden(C_78,A_79)
      | ~ r2_hidden(C_78,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_796,plain,(
    ! [A_123,B_124,A_125] :
      ( r2_hidden('#skF_2'(A_123,B_124),A_125)
      | ~ m1_subset_1(A_123,k1_zfmisc_1(A_125))
      | r1_tarski(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_839,plain,(
    ! [A_128,A_129] :
      ( ~ m1_subset_1(A_128,k1_zfmisc_1(A_129))
      | r1_tarski(A_128,A_129) ) ),
    inference(resolution,[status(thm)],[c_796,c_8])).

tff(c_890,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_373,c_839])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_79,plain,(
    ! [B_47,A_48] :
      ( v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_90,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_240,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_225])).

tff(c_251,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_240])).

tff(c_359,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_344])).

tff(c_369,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_359])).

tff(c_370,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_369])).

tff(c_1218,plain,(
    ! [A_146,B_147,C_148] :
      ( k9_subset_1(u1_struct_0(A_146),B_147,k2_pre_topc(A_146,C_148)) = C_148
      | ~ r1_tarski(C_148,B_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ v2_tex_2(B_147,A_146)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1227,plain,(
    ! [B_147] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_147,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_147)
      | ~ v2_tex_2(B_147,'#skF_4')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_370,c_1218])).

tff(c_1247,plain,(
    ! [B_147] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_147,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_147)
      | ~ v2_tex_2(B_147,'#skF_4')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1227])).

tff(c_1510,plain,(
    ! [B_166] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_166,k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski('#skF_6'),B_166)
      | ~ v2_tex_2(B_166,'#skF_4')
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1247])).

tff(c_44,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_275,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_251,c_44])).

tff(c_1516,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_275])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_890,c_1516])).

tff(c_1526,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1532,plain,(
    ! [A_169] :
      ( ~ v1_xboole_0(u1_struct_0(A_169))
      | ~ l1_struct_0(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1535,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1526,c_1532])).

tff(c_1538,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1535])).

tff(c_1541,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_1538])).

tff(c_1545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.66  
% 4.00/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.66  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.00/1.66  
% 4.00/1.66  %Foreground sorts:
% 4.00/1.66  
% 4.00/1.66  
% 4.00/1.66  %Background operators:
% 4.00/1.66  
% 4.00/1.66  
% 4.00/1.66  %Foreground operators:
% 4.00/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.00/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.00/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.00/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.00/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.00/1.66  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.00/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.00/1.66  tff('#skF_5', type, '#skF_5': $i).
% 4.00/1.66  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.00/1.66  tff('#skF_6', type, '#skF_6': $i).
% 4.00/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.00/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.66  tff('#skF_4', type, '#skF_4': $i).
% 4.00/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.00/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.00/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.00/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.00/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.00/1.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.00/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.66  
% 4.12/1.67  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 4.12/1.67  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.12/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.12/1.67  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.12/1.67  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.12/1.67  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.12/1.67  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.12/1.67  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.12/1.67  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.12/1.67  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.12/1.67  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_28, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.12/1.67  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_50, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_60, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.67  tff(c_64, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_60])).
% 4.12/1.67  tff(c_108, plain, (![B_58, A_59]: (m1_subset_1(B_58, A_59) | ~r2_hidden(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.67  tff(c_120, plain, (m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_108])).
% 4.12/1.67  tff(c_126, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_120])).
% 4.12/1.67  tff(c_225, plain, (![A_76, B_77]: (k6_domain_1(A_76, B_77)=k1_tarski(B_77) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.12/1.67  tff(c_231, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_126, c_225])).
% 4.12/1.67  tff(c_244, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_231])).
% 4.12/1.67  tff(c_344, plain, (![A_87, B_88]: (m1_subset_1(k6_domain_1(A_87, B_88), k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.12/1.67  tff(c_362, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_244, c_344])).
% 4.12/1.67  tff(c_372, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_362])).
% 4.12/1.67  tff(c_373, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_372])).
% 4.12/1.67  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.67  tff(c_252, plain, (![C_78, A_79, B_80]: (r2_hidden(C_78, A_79) | ~r2_hidden(C_78, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.12/1.67  tff(c_796, plain, (![A_123, B_124, A_125]: (r2_hidden('#skF_2'(A_123, B_124), A_125) | ~m1_subset_1(A_123, k1_zfmisc_1(A_125)) | r1_tarski(A_123, B_124))), inference(resolution, [status(thm)], [c_10, c_252])).
% 4.12/1.67  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.67  tff(c_839, plain, (![A_128, A_129]: (~m1_subset_1(A_128, k1_zfmisc_1(A_129)) | r1_tarski(A_128, A_129))), inference(resolution, [status(thm)], [c_796, c_8])).
% 4.12/1.67  tff(c_890, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_373, c_839])).
% 4.12/1.67  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.67  tff(c_79, plain, (![B_47, A_48]: (v1_xboole_0(B_47) | ~m1_subset_1(B_47, A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.67  tff(c_89, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_79])).
% 4.12/1.67  tff(c_90, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_89])).
% 4.12/1.67  tff(c_240, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_225])).
% 4.12/1.67  tff(c_251, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_90, c_240])).
% 4.12/1.67  tff(c_359, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_344])).
% 4.12/1.67  tff(c_369, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_359])).
% 4.12/1.67  tff(c_370, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_90, c_369])).
% 4.12/1.67  tff(c_1218, plain, (![A_146, B_147, C_148]: (k9_subset_1(u1_struct_0(A_146), B_147, k2_pre_topc(A_146, C_148))=C_148 | ~r1_tarski(C_148, B_147) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_146))) | ~v2_tex_2(B_147, A_146) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.12/1.67  tff(c_1227, plain, (![B_147]: (k9_subset_1(u1_struct_0('#skF_4'), B_147, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_147) | ~v2_tex_2(B_147, '#skF_4') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_370, c_1218])).
% 4.12/1.67  tff(c_1247, plain, (![B_147]: (k9_subset_1(u1_struct_0('#skF_4'), B_147, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_147) | ~v2_tex_2(B_147, '#skF_4') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1227])).
% 4.12/1.68  tff(c_1510, plain, (![B_166]: (k9_subset_1(u1_struct_0('#skF_4'), B_166, k2_pre_topc('#skF_4', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), B_166) | ~v2_tex_2(B_166, '#skF_4') | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_1247])).
% 4.12/1.68  tff(c_44, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.12/1.68  tff(c_275, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_251, c_44])).
% 4.12/1.68  tff(c_1516, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1510, c_275])).
% 4.12/1.68  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_890, c_1516])).
% 4.12/1.68  tff(c_1526, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_89])).
% 4.12/1.68  tff(c_1532, plain, (![A_169]: (~v1_xboole_0(u1_struct_0(A_169)) | ~l1_struct_0(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.12/1.68  tff(c_1535, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1526, c_1532])).
% 4.12/1.68  tff(c_1538, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_1535])).
% 4.12/1.68  tff(c_1541, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_1538])).
% 4.12/1.68  tff(c_1545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1541])).
% 4.12/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.68  
% 4.12/1.68  Inference rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Ref     : 0
% 4.12/1.68  #Sup     : 342
% 4.12/1.68  #Fact    : 0
% 4.12/1.68  #Define  : 0
% 4.12/1.68  #Split   : 8
% 4.12/1.68  #Chain   : 0
% 4.12/1.68  #Close   : 0
% 4.12/1.68  
% 4.12/1.68  Ordering : KBO
% 4.12/1.68  
% 4.12/1.68  Simplification rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Subsume      : 82
% 4.12/1.68  #Demod        : 62
% 4.12/1.68  #Tautology    : 71
% 4.12/1.68  #SimpNegUnit  : 52
% 4.12/1.68  #BackRed      : 1
% 4.12/1.68  
% 4.12/1.68  #Partial instantiations: 0
% 4.12/1.68  #Strategies tried      : 1
% 4.12/1.68  
% 4.12/1.68  Timing (in seconds)
% 4.12/1.68  ----------------------
% 4.12/1.68  Preprocessing        : 0.34
% 4.12/1.68  Parsing              : 0.18
% 4.12/1.68  CNF conversion       : 0.03
% 4.12/1.68  Main loop            : 0.57
% 4.12/1.68  Inferencing          : 0.20
% 4.12/1.68  Reduction            : 0.17
% 4.12/1.68  Demodulation         : 0.11
% 4.12/1.68  BG Simplification    : 0.03
% 4.12/1.68  Subsumption          : 0.12
% 4.12/1.68  Abstraction          : 0.03
% 4.12/1.68  MUC search           : 0.00
% 4.12/1.68  Cooper               : 0.00
% 4.12/1.68  Total                : 0.94
% 4.12/1.68  Index Insertion      : 0.00
% 4.12/1.68  Index Deletion       : 0.00
% 4.12/1.68  Index Matching       : 0.00
% 4.12/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
