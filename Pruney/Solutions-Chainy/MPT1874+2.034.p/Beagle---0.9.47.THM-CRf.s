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

% Result     : Theorem 7.30s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 201 expanded)
%              Number of leaves         :   37 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 542 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_106,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_44,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_95,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k1_tarski(A_68),k1_zfmisc_1(B_69))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_95,c_28])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_76,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_102,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_74] : r1_tarski(A_74,A_74) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_123,plain,(
    ! [C_82,B_83,A_84] :
      ( r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_263,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden('#skF_2'(A_107,B_108),B_109)
      | ~ r1_tarski(A_107,B_109)
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_387,plain,(
    ! [A_135,B_136,B_137,B_138] :
      ( r2_hidden('#skF_2'(A_135,B_136),B_137)
      | ~ r1_tarski(B_138,B_137)
      | ~ r1_tarski(A_135,B_138)
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_263,c_6])).

tff(c_531,plain,(
    ! [A_160,B_161,B_162,A_163] :
      ( r2_hidden('#skF_2'(A_160,B_161),B_162)
      | ~ r1_tarski(A_160,k1_tarski(A_163))
      | r1_tarski(A_160,B_161)
      | ~ r2_hidden(A_163,B_162) ) ),
    inference(resolution,[status(thm)],[c_99,c_387])).

tff(c_544,plain,(
    ! [A_164,B_165,B_166] :
      ( r2_hidden('#skF_2'(k1_tarski(A_164),B_165),B_166)
      | r1_tarski(k1_tarski(A_164),B_165)
      | ~ r2_hidden(A_164,B_166) ) ),
    inference(resolution,[status(thm)],[c_110,c_531])).

tff(c_3439,plain,(
    ! [A_328,B_329,B_330,B_331] :
      ( r2_hidden('#skF_2'(k1_tarski(A_328),B_329),B_330)
      | ~ r1_tarski(B_331,B_330)
      | r1_tarski(k1_tarski(A_328),B_329)
      | ~ r2_hidden(A_328,B_331) ) ),
    inference(resolution,[status(thm)],[c_544,c_6])).

tff(c_3455,plain,(
    ! [A_332,B_333] :
      ( r2_hidden('#skF_2'(k1_tarski(A_332),B_333),u1_struct_0('#skF_4'))
      | r1_tarski(k1_tarski(A_332),B_333)
      | ~ r2_hidden(A_332,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_80,c_3439])).

tff(c_3472,plain,(
    ! [A_332] :
      ( r1_tarski(k1_tarski(A_332),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_332,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3455,c_8])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3774,plain,(
    ! [A_358,B_359,C_360] :
      ( k9_subset_1(u1_struct_0(A_358),B_359,k2_pre_topc(A_358,C_360)) = C_360
      | ~ r1_tarski(C_360,B_359)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ v2_tex_2(B_359,A_358)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5737,plain,(
    ! [A_426,B_427,A_428] :
      ( k9_subset_1(u1_struct_0(A_426),B_427,k2_pre_topc(A_426,A_428)) = A_428
      | ~ r1_tarski(A_428,B_427)
      | ~ v2_tex_2(B_427,A_426)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426)
      | ~ r1_tarski(A_428,u1_struct_0(A_426)) ) ),
    inference(resolution,[status(thm)],[c_30,c_3774])).

tff(c_5747,plain,(
    ! [A_428] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_428)) = A_428
      | ~ r1_tarski(A_428,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_428,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_5737])).

tff(c_5753,plain,(
    ! [A_428] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_428)) = A_428
      | ~ r1_tarski(A_428,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_428,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_5747])).

tff(c_5842,plain,(
    ! [A_430] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_430)) = A_430
      | ~ r1_tarski(A_430,'#skF_5')
      | ~ r1_tarski(A_430,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5753])).

tff(c_133,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_6',B_85)
      | ~ r1_tarski('#skF_5',B_85) ) ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [B_88] :
      ( ~ v1_xboole_0(B_88)
      | ~ r1_tarski('#skF_5',B_88) ) ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_172,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_158])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_141,plain,(
    ! [A_86,B_87] :
      ( k6_domain_1(A_86,B_87) = k1_tarski(B_87)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_157,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_141])).

tff(c_173,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_157])).

tff(c_42,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_174,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_42])).

tff(c_5881,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_174])).

tff(c_5889,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5881])).

tff(c_5964,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_3472,c_5889])).

tff(c_5978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5964])).

tff(c_5979,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5881])).

tff(c_5986,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_5979])).

tff(c_5991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.30/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.56  
% 7.30/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.56  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 7.30/2.56  
% 7.30/2.56  %Foreground sorts:
% 7.30/2.56  
% 7.30/2.56  
% 7.30/2.56  %Background operators:
% 7.30/2.56  
% 7.30/2.56  
% 7.30/2.56  %Foreground operators:
% 7.30/2.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.30/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.30/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.30/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.30/2.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.30/2.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.30/2.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.30/2.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.30/2.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.30/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.30/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.30/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.30/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.30/2.56  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.30/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.30/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.30/2.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.30/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.30/2.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.30/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.30/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.30/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.30/2.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.30/2.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.30/2.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.30/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.30/2.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.30/2.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.30/2.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.30/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.30/2.56  
% 7.30/2.58  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 7.30/2.58  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 7.30/2.58  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.30/2.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.30/2.58  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 7.30/2.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.30/2.58  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.30/2.58  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_95, plain, (![A_68, B_69]: (m1_subset_1(k1_tarski(A_68), k1_zfmisc_1(B_69)) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.30/2.58  tff(c_28, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.30/2.58  tff(c_99, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_95, c_28])).
% 7.30/2.58  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_76, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.30/2.58  tff(c_80, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_76])).
% 7.30/2.58  tff(c_102, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.30/2.58  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.30/2.58  tff(c_110, plain, (![A_74]: (r1_tarski(A_74, A_74))), inference(resolution, [status(thm)], [c_102, c_8])).
% 7.30/2.58  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.30/2.58  tff(c_123, plain, (![C_82, B_83, A_84]: (r2_hidden(C_82, B_83) | ~r2_hidden(C_82, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.30/2.58  tff(c_263, plain, (![A_107, B_108, B_109]: (r2_hidden('#skF_2'(A_107, B_108), B_109) | ~r1_tarski(A_107, B_109) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_10, c_123])).
% 7.30/2.58  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.30/2.58  tff(c_387, plain, (![A_135, B_136, B_137, B_138]: (r2_hidden('#skF_2'(A_135, B_136), B_137) | ~r1_tarski(B_138, B_137) | ~r1_tarski(A_135, B_138) | r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_263, c_6])).
% 7.30/2.58  tff(c_531, plain, (![A_160, B_161, B_162, A_163]: (r2_hidden('#skF_2'(A_160, B_161), B_162) | ~r1_tarski(A_160, k1_tarski(A_163)) | r1_tarski(A_160, B_161) | ~r2_hidden(A_163, B_162))), inference(resolution, [status(thm)], [c_99, c_387])).
% 7.30/2.58  tff(c_544, plain, (![A_164, B_165, B_166]: (r2_hidden('#skF_2'(k1_tarski(A_164), B_165), B_166) | r1_tarski(k1_tarski(A_164), B_165) | ~r2_hidden(A_164, B_166))), inference(resolution, [status(thm)], [c_110, c_531])).
% 7.30/2.58  tff(c_3439, plain, (![A_328, B_329, B_330, B_331]: (r2_hidden('#skF_2'(k1_tarski(A_328), B_329), B_330) | ~r1_tarski(B_331, B_330) | r1_tarski(k1_tarski(A_328), B_329) | ~r2_hidden(A_328, B_331))), inference(resolution, [status(thm)], [c_544, c_6])).
% 7.30/2.58  tff(c_3455, plain, (![A_332, B_333]: (r2_hidden('#skF_2'(k1_tarski(A_332), B_333), u1_struct_0('#skF_4')) | r1_tarski(k1_tarski(A_332), B_333) | ~r2_hidden(A_332, '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_3439])).
% 7.30/2.58  tff(c_3472, plain, (![A_332]: (r1_tarski(k1_tarski(A_332), u1_struct_0('#skF_4')) | ~r2_hidden(A_332, '#skF_5'))), inference(resolution, [status(thm)], [c_3455, c_8])).
% 7.30/2.58  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_48, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_30, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.30/2.58  tff(c_3774, plain, (![A_358, B_359, C_360]: (k9_subset_1(u1_struct_0(A_358), B_359, k2_pre_topc(A_358, C_360))=C_360 | ~r1_tarski(C_360, B_359) | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(A_358))) | ~v2_tex_2(B_359, A_358) | ~m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0(A_358))) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.30/2.58  tff(c_5737, plain, (![A_426, B_427, A_428]: (k9_subset_1(u1_struct_0(A_426), B_427, k2_pre_topc(A_426, A_428))=A_428 | ~r1_tarski(A_428, B_427) | ~v2_tex_2(B_427, A_426) | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426) | ~r1_tarski(A_428, u1_struct_0(A_426)))), inference(resolution, [status(thm)], [c_30, c_3774])).
% 7.30/2.58  tff(c_5747, plain, (![A_428]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_428))=A_428 | ~r1_tarski(A_428, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_428, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_5737])).
% 7.30/2.58  tff(c_5753, plain, (![A_428]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_428))=A_428 | ~r1_tarski(A_428, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_428, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_5747])).
% 7.30/2.58  tff(c_5842, plain, (![A_430]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_430))=A_430 | ~r1_tarski(A_430, '#skF_5') | ~r1_tarski(A_430, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_5753])).
% 7.30/2.58  tff(c_133, plain, (![B_85]: (r2_hidden('#skF_6', B_85) | ~r1_tarski('#skF_5', B_85))), inference(resolution, [status(thm)], [c_44, c_123])).
% 7.30/2.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.58  tff(c_158, plain, (![B_88]: (~v1_xboole_0(B_88) | ~r1_tarski('#skF_5', B_88))), inference(resolution, [status(thm)], [c_133, c_2])).
% 7.30/2.58  tff(c_172, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_158])).
% 7.30/2.58  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_141, plain, (![A_86, B_87]: (k6_domain_1(A_86, B_87)=k1_tarski(B_87) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.30/2.58  tff(c_157, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_141])).
% 7.30/2.58  tff(c_173, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_172, c_157])).
% 7.30/2.58  tff(c_42, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.30/2.58  tff(c_174, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_42])).
% 7.30/2.58  tff(c_5881, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5842, c_174])).
% 7.30/2.58  tff(c_5889, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_5881])).
% 7.30/2.58  tff(c_5964, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_3472, c_5889])).
% 7.30/2.58  tff(c_5978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_5964])).
% 7.30/2.58  tff(c_5979, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_5881])).
% 7.30/2.58  tff(c_5986, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_99, c_5979])).
% 7.30/2.58  tff(c_5991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_5986])).
% 7.30/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.58  
% 7.30/2.58  Inference rules
% 7.30/2.58  ----------------------
% 7.30/2.58  #Ref     : 0
% 7.30/2.58  #Sup     : 1523
% 7.30/2.58  #Fact    : 0
% 7.30/2.58  #Define  : 0
% 7.30/2.58  #Split   : 12
% 7.30/2.58  #Chain   : 0
% 7.30/2.58  #Close   : 0
% 7.30/2.58  
% 7.30/2.58  Ordering : KBO
% 7.30/2.58  
% 7.30/2.58  Simplification rules
% 7.30/2.58  ----------------------
% 7.30/2.58  #Subsume      : 400
% 7.30/2.58  #Demod        : 202
% 7.30/2.58  #Tautology    : 178
% 7.30/2.58  #SimpNegUnit  : 24
% 7.30/2.58  #BackRed      : 1
% 7.30/2.58  
% 7.30/2.58  #Partial instantiations: 0
% 7.30/2.58  #Strategies tried      : 1
% 7.30/2.58  
% 7.30/2.58  Timing (in seconds)
% 7.30/2.58  ----------------------
% 7.30/2.58  Preprocessing        : 0.35
% 7.30/2.58  Parsing              : 0.18
% 7.30/2.58  CNF conversion       : 0.03
% 7.30/2.58  Main loop            : 1.45
% 7.30/2.58  Inferencing          : 0.39
% 7.30/2.58  Reduction            : 0.37
% 7.30/2.58  Demodulation         : 0.24
% 7.30/2.58  BG Simplification    : 0.05
% 7.30/2.58  Subsumption          : 0.54
% 7.30/2.58  Abstraction          : 0.06
% 7.30/2.58  MUC search           : 0.00
% 7.30/2.58  Cooper               : 0.00
% 7.30/2.58  Total                : 1.83
% 7.30/2.58  Index Insertion      : 0.00
% 7.30/2.59  Index Deletion       : 0.00
% 7.30/2.59  Index Matching       : 0.00
% 7.30/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
