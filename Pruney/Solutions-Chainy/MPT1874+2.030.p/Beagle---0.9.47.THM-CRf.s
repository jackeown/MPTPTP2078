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
% DateTime   : Thu Dec  3 10:29:41 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 175 expanded)
%              Number of leaves         :   39 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 457 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1939,plain,(
    ! [A_261,B_262,C_263] :
      ( r1_tarski(k2_tarski(A_261,B_262),C_263)
      | ~ r2_hidden(B_262,C_263)
      | ~ r2_hidden(A_261,C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1965,plain,(
    ! [A_264,C_265] :
      ( r1_tarski(k1_tarski(A_264),C_265)
      | ~ r2_hidden(A_264,C_265)
      | ~ r2_hidden(A_264,C_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1939])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_76,plain,(
    ! [B_62,A_63] :
      ( ~ r2_hidden(B_62,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_136,plain,(
    ! [B_80,A_81] :
      ( m1_subset_1(B_80,A_81)
      | ~ r2_hidden(B_80,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,
    ( m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_146,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_142])).

tff(c_230,plain,(
    ! [A_106,B_107] :
      ( k6_domain_1(A_106,B_107) = k1_tarski(B_107)
      | ~ m1_subset_1(B_107,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_236,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_230])).

tff(c_252,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_236])).

tff(c_407,plain,(
    ! [A_122,B_123] :
      ( m1_subset_1(k6_domain_1(A_122,B_123),k1_zfmisc_1(A_122))
      | ~ m1_subset_1(B_123,A_122)
      | v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_431,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_407])).

tff(c_443,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_431])).

tff(c_444,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_443])).

tff(c_36,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_464,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_444,c_36])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_86,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(B_65)
      | ~ m1_subset_1(B_65,A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_86])).

tff(c_97,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_248,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_230])).

tff(c_260,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_248])).

tff(c_428,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_407])).

tff(c_440,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_428])).

tff(c_441,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_440])).

tff(c_1343,plain,(
    ! [A_190,B_191,C_192] :
      ( k9_subset_1(u1_struct_0(A_190),B_191,k2_pre_topc(A_190,C_192)) = C_192
      | ~ r1_tarski(C_192,B_191)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ v2_tex_2(B_191,A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1351,plain,(
    ! [B_191] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_191,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_191)
      | ~ v2_tex_2(B_191,'#skF_3')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_441,c_1343])).

tff(c_1377,plain,(
    ! [B_191] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_191,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_191)
      | ~ v2_tex_2(B_191,'#skF_3')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1351])).

tff(c_1721,plain,(
    ! [B_212] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_212,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_212)
      | ~ v2_tex_2(B_212,'#skF_3')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1377])).

tff(c_52,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_265,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_52])).

tff(c_1727,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_265])).

tff(c_1735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_464,c_1727])).

tff(c_1737,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1743,plain,(
    ! [A_215,B_216] :
      ( r1_tarski(A_215,B_216)
      | ~ m1_subset_1(A_215,k1_zfmisc_1(B_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1752,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_1743])).

tff(c_1815,plain,(
    ! [A_234,C_235,B_236] :
      ( r1_tarski(A_234,C_235)
      | ~ r1_tarski(B_236,C_235)
      | ~ r1_tarski(A_234,B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1819,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_237,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1752,c_1815])).

tff(c_1771,plain,(
    ! [B_221,C_222,A_223] :
      ( r2_hidden(B_221,C_222)
      | ~ r1_tarski(k2_tarski(A_223,B_221),C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1774,plain,(
    ! [A_8,C_222] :
      ( r2_hidden(A_8,C_222)
      | ~ r1_tarski(k1_tarski(A_8),C_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1771])).

tff(c_1840,plain,(
    ! [A_242] :
      ( r2_hidden(A_242,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_242),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1819,c_1774])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1846,plain,(
    ! [A_242] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_242),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1840,c_2])).

tff(c_1851,plain,(
    ! [A_242] : ~ r1_tarski(k1_tarski(A_242),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1846])).

tff(c_1978,plain,(
    ! [A_264] : ~ r2_hidden(A_264,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1965,c_1851])).

tff(c_1982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1978,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.73  
% 4.10/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.73  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.10/1.73  
% 4.10/1.73  %Foreground sorts:
% 4.10/1.73  
% 4.10/1.73  
% 4.10/1.73  %Background operators:
% 4.10/1.73  
% 4.10/1.73  
% 4.10/1.73  %Foreground operators:
% 4.10/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.10/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.10/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.10/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.10/1.73  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.10/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.10/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.10/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.73  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.10/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.10/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.10/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.10/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.10/1.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.10/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.10/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.10/1.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.10/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.73  
% 4.10/1.75  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.10/1.75  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.10/1.75  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.10/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.10/1.75  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.10/1.75  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.10/1.75  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.10/1.75  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.10/1.75  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.10/1.75  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.10/1.75  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.75  tff(c_1939, plain, (![A_261, B_262, C_263]: (r1_tarski(k2_tarski(A_261, B_262), C_263) | ~r2_hidden(B_262, C_263) | ~r2_hidden(A_261, C_263))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.10/1.75  tff(c_1965, plain, (![A_264, C_265]: (r1_tarski(k1_tarski(A_264), C_265) | ~r2_hidden(A_264, C_265) | ~r2_hidden(A_264, C_265))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1939])).
% 4.10/1.75  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_58, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_76, plain, (![B_62, A_63]: (~r2_hidden(B_62, A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.75  tff(c_80, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_76])).
% 4.10/1.75  tff(c_136, plain, (![B_80, A_81]: (m1_subset_1(B_80, A_81) | ~r2_hidden(B_80, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.10/1.75  tff(c_142, plain, (m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_136])).
% 4.10/1.75  tff(c_146, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_142])).
% 4.10/1.75  tff(c_230, plain, (![A_106, B_107]: (k6_domain_1(A_106, B_107)=k1_tarski(B_107) | ~m1_subset_1(B_107, A_106) | v1_xboole_0(A_106))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.10/1.75  tff(c_236, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_146, c_230])).
% 4.10/1.75  tff(c_252, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_236])).
% 4.10/1.75  tff(c_407, plain, (![A_122, B_123]: (m1_subset_1(k6_domain_1(A_122, B_123), k1_zfmisc_1(A_122)) | ~m1_subset_1(B_123, A_122) | v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.75  tff(c_431, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_252, c_407])).
% 4.10/1.75  tff(c_443, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_431])).
% 4.10/1.75  tff(c_444, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_443])).
% 4.10/1.75  tff(c_36, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.75  tff(c_464, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_444, c_36])).
% 4.10/1.75  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_56, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_86, plain, (![B_65, A_66]: (v1_xboole_0(B_65) | ~m1_subset_1(B_65, A_66) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.10/1.75  tff(c_96, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_86])).
% 4.10/1.75  tff(c_97, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_96])).
% 4.10/1.75  tff(c_248, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_230])).
% 4.10/1.75  tff(c_260, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_97, c_248])).
% 4.10/1.75  tff(c_428, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_407])).
% 4.10/1.75  tff(c_440, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_428])).
% 4.10/1.75  tff(c_441, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_97, c_440])).
% 4.10/1.75  tff(c_1343, plain, (![A_190, B_191, C_192]: (k9_subset_1(u1_struct_0(A_190), B_191, k2_pre_topc(A_190, C_192))=C_192 | ~r1_tarski(C_192, B_191) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(A_190))) | ~v2_tex_2(B_191, A_190) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.10/1.75  tff(c_1351, plain, (![B_191]: (k9_subset_1(u1_struct_0('#skF_3'), B_191, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_191) | ~v2_tex_2(B_191, '#skF_3') | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_441, c_1343])).
% 4.10/1.75  tff(c_1377, plain, (![B_191]: (k9_subset_1(u1_struct_0('#skF_3'), B_191, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_191) | ~v2_tex_2(B_191, '#skF_3') | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1351])).
% 4.10/1.75  tff(c_1721, plain, (![B_212]: (k9_subset_1(u1_struct_0('#skF_3'), B_212, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_212) | ~v2_tex_2(B_212, '#skF_3') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_1377])).
% 4.10/1.75  tff(c_52, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.10/1.75  tff(c_265, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_52])).
% 4.10/1.75  tff(c_1727, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1721, c_265])).
% 4.10/1.75  tff(c_1735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_464, c_1727])).
% 4.10/1.75  tff(c_1737, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_96])).
% 4.10/1.75  tff(c_1743, plain, (![A_215, B_216]: (r1_tarski(A_215, B_216) | ~m1_subset_1(A_215, k1_zfmisc_1(B_216)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.75  tff(c_1752, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_1743])).
% 4.10/1.75  tff(c_1815, plain, (![A_234, C_235, B_236]: (r1_tarski(A_234, C_235) | ~r1_tarski(B_236, C_235) | ~r1_tarski(A_234, B_236))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.10/1.75  tff(c_1819, plain, (![A_237]: (r1_tarski(A_237, u1_struct_0('#skF_3')) | ~r1_tarski(A_237, '#skF_4'))), inference(resolution, [status(thm)], [c_1752, c_1815])).
% 4.10/1.75  tff(c_1771, plain, (![B_221, C_222, A_223]: (r2_hidden(B_221, C_222) | ~r1_tarski(k2_tarski(A_223, B_221), C_222))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.10/1.75  tff(c_1774, plain, (![A_8, C_222]: (r2_hidden(A_8, C_222) | ~r1_tarski(k1_tarski(A_8), C_222))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1771])).
% 4.10/1.75  tff(c_1840, plain, (![A_242]: (r2_hidden(A_242, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_242), '#skF_4'))), inference(resolution, [status(thm)], [c_1819, c_1774])).
% 4.10/1.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.75  tff(c_1846, plain, (![A_242]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_242), '#skF_4'))), inference(resolution, [status(thm)], [c_1840, c_2])).
% 4.10/1.75  tff(c_1851, plain, (![A_242]: (~r1_tarski(k1_tarski(A_242), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1846])).
% 4.10/1.75  tff(c_1978, plain, (![A_264]: (~r2_hidden(A_264, '#skF_4'))), inference(resolution, [status(thm)], [c_1965, c_1851])).
% 4.10/1.75  tff(c_1982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1978, c_54])).
% 4.10/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.75  
% 4.10/1.75  Inference rules
% 4.10/1.75  ----------------------
% 4.10/1.75  #Ref     : 0
% 4.10/1.75  #Sup     : 421
% 4.10/1.75  #Fact    : 0
% 4.10/1.75  #Define  : 0
% 4.10/1.75  #Split   : 12
% 4.10/1.75  #Chain   : 0
% 4.10/1.75  #Close   : 0
% 4.10/1.75  
% 4.10/1.75  Ordering : KBO
% 4.10/1.75  
% 4.10/1.75  Simplification rules
% 4.10/1.75  ----------------------
% 4.10/1.75  #Subsume      : 64
% 4.10/1.75  #Demod        : 84
% 4.10/1.75  #Tautology    : 111
% 4.10/1.75  #SimpNegUnit  : 63
% 4.10/1.75  #BackRed      : 4
% 4.10/1.75  
% 4.10/1.75  #Partial instantiations: 0
% 4.10/1.75  #Strategies tried      : 1
% 4.10/1.75  
% 4.10/1.75  Timing (in seconds)
% 4.10/1.75  ----------------------
% 4.10/1.75  Preprocessing        : 0.35
% 4.10/1.75  Parsing              : 0.19
% 4.10/1.75  CNF conversion       : 0.03
% 4.10/1.75  Main loop            : 0.63
% 4.10/1.75  Inferencing          : 0.22
% 4.10/1.75  Reduction            : 0.19
% 4.10/1.75  Demodulation         : 0.13
% 4.10/1.75  BG Simplification    : 0.03
% 4.10/1.75  Subsumption          : 0.13
% 4.10/1.75  Abstraction          : 0.03
% 4.10/1.75  MUC search           : 0.00
% 4.10/1.75  Cooper               : 0.00
% 4.10/1.75  Total                : 1.01
% 4.10/1.75  Index Insertion      : 0.00
% 4.10/1.75  Index Deletion       : 0.00
% 4.10/1.75  Index Matching       : 0.00
% 4.10/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
