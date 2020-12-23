%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 167 expanded)
%              Number of leaves         :   38 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 454 expanded)
%              Number of equality atoms :   16 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
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

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_135,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(B_71,A_72)
      | ~ r2_hidden(B_71,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,
    ( m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_135])).

tff(c_140,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_24,plain,(
    ! [A_31] : k2_subset_1(A_31) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_32] : m1_subset_1(k2_subset_1(A_32),k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [A_32] : m1_subset_1(A_32,k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_148,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ v1_xboole_0(C_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(C_79))
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_162,plain,(
    ! [A_82,A_83] :
      ( ~ v1_xboole_0(A_82)
      | ~ r2_hidden(A_83,A_82) ) ),
    inference(resolution,[status(thm)],[c_61,c_148])).

tff(c_168,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_162])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_168])).

tff(c_175,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_174,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_236,plain,(
    ! [A_102,B_103] :
      ( k6_domain_1(A_102,B_103) = k1_tarski(B_103)
      | ~ m1_subset_1(B_103,A_102)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_239,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_236])).

tff(c_257,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_239])).

tff(c_280,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k6_domain_1(A_104,B_105),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_300,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_280])).

tff(c_312,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_300])).

tff(c_313,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_312])).

tff(c_28,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_328,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_28])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_111,plain,(
    ! [B_68,A_69] :
      ( v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_111])).

tff(c_133,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_254,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_236])).

tff(c_266,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_254])).

tff(c_297,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_280])).

tff(c_309,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_297])).

tff(c_310,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_309])).

tff(c_2032,plain,(
    ! [A_158,B_159,C_160] :
      ( k9_subset_1(u1_struct_0(A_158),B_159,k2_pre_topc(A_158,C_160)) = C_160
      | ~ r1_tarski(C_160,B_159)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ v2_tex_2(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2036,plain,(
    ! [B_159] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_159,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_159)
      | ~ v2_tex_2(B_159,'#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_310,c_2032])).

tff(c_2054,plain,(
    ! [B_159] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_159,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_159)
      | ~ v2_tex_2(B_159,'#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2036])).

tff(c_2289,plain,(
    ! [B_164] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_164,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_164)
      | ~ v2_tex_2(B_164,'#skF_2')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2054])).

tff(c_46,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_271,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_266,c_46])).

tff(c_2295,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2289,c_271])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_328,c_2295])).

tff(c_2305,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_2320,plain,(
    ! [C_173,B_174,A_175] :
      ( ~ v1_xboole_0(C_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(C_173))
      | ~ r2_hidden(A_175,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2327,plain,(
    ! [A_175] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_175,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_2320])).

tff(c_2334,plain,(
    ! [A_175] : ~ r2_hidden(A_175,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2305,c_2327])).

tff(c_2337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2334,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.70  
% 4.11/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.70  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.11/1.70  
% 4.11/1.70  %Foreground sorts:
% 4.11/1.70  
% 4.11/1.70  
% 4.11/1.70  %Background operators:
% 4.11/1.70  
% 4.11/1.70  
% 4.11/1.70  %Foreground operators:
% 4.11/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.11/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.11/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.11/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.11/1.70  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.11/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.11/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.11/1.70  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.11/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.11/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.11/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.11/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.11/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.11/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.11/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.11/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.11/1.70  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.11/1.70  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.11/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.70  
% 4.11/1.73  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 4.11/1.73  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.11/1.73  tff(f_54, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.11/1.73  tff(f_56, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.11/1.73  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.11/1.73  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.11/1.73  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.11/1.73  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.11/1.73  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 4.11/1.73  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_52, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_135, plain, (![B_71, A_72]: (m1_subset_1(B_71, A_72) | ~r2_hidden(B_71, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.11/1.73  tff(c_139, plain, (m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_135])).
% 4.11/1.73  tff(c_140, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_139])).
% 4.11/1.73  tff(c_24, plain, (![A_31]: (k2_subset_1(A_31)=A_31)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.11/1.73  tff(c_26, plain, (![A_32]: (m1_subset_1(k2_subset_1(A_32), k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.11/1.73  tff(c_61, plain, (![A_32]: (m1_subset_1(A_32, k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 4.11/1.73  tff(c_148, plain, (![C_79, B_80, A_81]: (~v1_xboole_0(C_79) | ~m1_subset_1(B_80, k1_zfmisc_1(C_79)) | ~r2_hidden(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.11/1.73  tff(c_162, plain, (![A_82, A_83]: (~v1_xboole_0(A_82) | ~r2_hidden(A_83, A_82))), inference(resolution, [status(thm)], [c_61, c_148])).
% 4.11/1.73  tff(c_168, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_162])).
% 4.11/1.73  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_168])).
% 4.11/1.73  tff(c_175, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_139])).
% 4.11/1.73  tff(c_174, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_139])).
% 4.11/1.73  tff(c_236, plain, (![A_102, B_103]: (k6_domain_1(A_102, B_103)=k1_tarski(B_103) | ~m1_subset_1(B_103, A_102) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.73  tff(c_239, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_174, c_236])).
% 4.11/1.73  tff(c_257, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_175, c_239])).
% 4.11/1.73  tff(c_280, plain, (![A_104, B_105]: (m1_subset_1(k6_domain_1(A_104, B_105), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.11/1.73  tff(c_300, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_257, c_280])).
% 4.11/1.73  tff(c_312, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_300])).
% 4.11/1.73  tff(c_313, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_175, c_312])).
% 4.11/1.73  tff(c_28, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.11/1.73  tff(c_328, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_313, c_28])).
% 4.11/1.73  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_111, plain, (![B_68, A_69]: (v1_xboole_0(B_68) | ~m1_subset_1(B_68, A_69) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.11/1.73  tff(c_131, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_111])).
% 4.11/1.73  tff(c_133, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_131])).
% 4.11/1.73  tff(c_254, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_236])).
% 4.11/1.73  tff(c_266, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_133, c_254])).
% 4.11/1.73  tff(c_297, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_280])).
% 4.11/1.73  tff(c_309, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_297])).
% 4.11/1.73  tff(c_310, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_133, c_309])).
% 4.11/1.73  tff(c_2032, plain, (![A_158, B_159, C_160]: (k9_subset_1(u1_struct_0(A_158), B_159, k2_pre_topc(A_158, C_160))=C_160 | ~r1_tarski(C_160, B_159) | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0(A_158))) | ~v2_tex_2(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.11/1.73  tff(c_2036, plain, (![B_159]: (k9_subset_1(u1_struct_0('#skF_2'), B_159, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_159) | ~v2_tex_2(B_159, '#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_310, c_2032])).
% 4.11/1.73  tff(c_2054, plain, (![B_159]: (k9_subset_1(u1_struct_0('#skF_2'), B_159, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_159) | ~v2_tex_2(B_159, '#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2036])).
% 4.11/1.73  tff(c_2289, plain, (![B_164]: (k9_subset_1(u1_struct_0('#skF_2'), B_164, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_164) | ~v2_tex_2(B_164, '#skF_2') | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_2054])).
% 4.11/1.73  tff(c_46, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.73  tff(c_271, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_266, c_46])).
% 4.11/1.73  tff(c_2295, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2289, c_271])).
% 4.11/1.73  tff(c_2303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_328, c_2295])).
% 4.11/1.73  tff(c_2305, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_131])).
% 4.11/1.73  tff(c_2320, plain, (![C_173, B_174, A_175]: (~v1_xboole_0(C_173) | ~m1_subset_1(B_174, k1_zfmisc_1(C_173)) | ~r2_hidden(A_175, B_174))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.11/1.73  tff(c_2327, plain, (![A_175]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_175, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_2320])).
% 4.11/1.73  tff(c_2334, plain, (![A_175]: (~r2_hidden(A_175, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2305, c_2327])).
% 4.11/1.73  tff(c_2337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2334, c_48])).
% 4.11/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.73  
% 4.11/1.73  Inference rules
% 4.11/1.73  ----------------------
% 4.11/1.73  #Ref     : 0
% 4.11/1.73  #Sup     : 463
% 4.11/1.73  #Fact    : 0
% 4.11/1.73  #Define  : 0
% 4.11/1.73  #Split   : 15
% 4.11/1.73  #Chain   : 0
% 4.11/1.73  #Close   : 0
% 4.11/1.73  
% 4.11/1.73  Ordering : KBO
% 4.11/1.73  
% 4.11/1.73  Simplification rules
% 4.11/1.73  ----------------------
% 4.11/1.73  #Subsume      : 66
% 4.11/1.73  #Demod        : 180
% 4.11/1.73  #Tautology    : 244
% 4.11/1.73  #SimpNegUnit  : 152
% 4.11/1.73  #BackRed      : 2
% 4.11/1.73  
% 4.11/1.73  #Partial instantiations: 0
% 4.11/1.73  #Strategies tried      : 1
% 4.11/1.73  
% 4.11/1.73  Timing (in seconds)
% 4.11/1.73  ----------------------
% 4.11/1.73  Preprocessing        : 0.33
% 4.11/1.73  Parsing              : 0.18
% 4.11/1.73  CNF conversion       : 0.02
% 4.11/1.73  Main loop            : 0.59
% 4.11/1.73  Inferencing          : 0.20
% 4.11/1.73  Reduction            : 0.20
% 4.11/1.73  Demodulation         : 0.14
% 4.11/1.73  BG Simplification    : 0.03
% 4.11/1.73  Subsumption          : 0.12
% 4.11/1.73  Abstraction          : 0.03
% 4.11/1.73  MUC search           : 0.00
% 4.11/1.73  Cooper               : 0.00
% 4.11/1.74  Total                : 0.99
% 4.11/1.74  Index Insertion      : 0.00
% 4.11/1.74  Index Deletion       : 0.00
% 4.11/1.74  Index Matching       : 0.00
% 4.11/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
