%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:44 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 115 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :   98 ( 288 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_85,axiom,(
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

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k2_tarski(A_76,B_77),C_78)
      | ~ r2_hidden(B_77,C_78)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [A_1,C_78] :
      ( r1_tarski(k1_tarski(A_1),C_78)
      | ~ r2_hidden(A_1,C_78)
      | ~ r2_hidden(A_1,C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_87,plain,(
    ! [C_67,B_68,A_69] :
      ( ~ v1_xboole_0(C_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [A_69] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_69,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_100,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_91,plain,(
    ! [A_70,B_71] :
      ( k6_domain_1(A_70,B_71) = k1_tarski(B_71)
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_101,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_99])).

tff(c_133,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k6_domain_1(A_81,B_82),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_133])).

tff(c_145,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_141])).

tff(c_146,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_145])).

tff(c_255,plain,(
    ! [A_114,B_115,C_116] :
      ( k9_subset_1(u1_struct_0(A_114),B_115,k2_pre_topc(A_114,C_116)) = C_116
      | ~ r1_tarski(C_116,B_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_259,plain,(
    ! [B_115] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_115,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_115)
      | ~ v2_tex_2(B_115,'#skF_2')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_146,c_255])).

tff(c_268,plain,(
    ! [B_115] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_115,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_115)
      | ~ v2_tex_2(B_115,'#skF_2')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_259])).

tff(c_306,plain,(
    ! [B_120] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_120,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_120)
      | ~ v2_tex_2(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_268])).

tff(c_36,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_102,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_101,c_36])).

tff(c_312,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_102])).

tff(c_319,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_312])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_319])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_323])).

tff(c_328,plain,(
    ! [A_69] : ~ r2_hidden(A_69,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.45  
% 2.49/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.45  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.45  
% 2.49/1.45  %Foreground sorts:
% 2.49/1.45  
% 2.49/1.45  
% 2.49/1.45  %Background operators:
% 2.49/1.45  
% 2.49/1.45  
% 2.49/1.45  %Foreground operators:
% 2.49/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.49/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.49/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.49/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.49/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.45  
% 2.84/1.47  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.84/1.47  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.47  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.84/1.47  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.84/1.47  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.84/1.47  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.84/1.47  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.84/1.47  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.47  tff(c_116, plain, (![A_76, B_77, C_78]: (r1_tarski(k2_tarski(A_76, B_77), C_78) | ~r2_hidden(B_77, C_78) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.84/1.47  tff(c_125, plain, (![A_1, C_78]: (r1_tarski(k1_tarski(A_1), C_78) | ~r2_hidden(A_1, C_78) | ~r2_hidden(A_1, C_78))), inference(superposition, [status(thm), theory('equality')], [c_2, c_116])).
% 2.84/1.47  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_42, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_87, plain, (![C_67, B_68, A_69]: (~v1_xboole_0(C_67) | ~m1_subset_1(B_68, k1_zfmisc_1(C_67)) | ~r2_hidden(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.47  tff(c_90, plain, (![A_69]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_69, '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.84/1.47  tff(c_100, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.84/1.47  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_91, plain, (![A_70, B_71]: (k6_domain_1(A_70, B_71)=k1_tarski(B_71) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.47  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_91])).
% 2.84/1.47  tff(c_101, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_100, c_99])).
% 2.84/1.47  tff(c_133, plain, (![A_81, B_82]: (m1_subset_1(k6_domain_1(A_81, B_82), k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.47  tff(c_141, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_133])).
% 2.84/1.47  tff(c_145, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_141])).
% 2.84/1.47  tff(c_146, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_100, c_145])).
% 2.84/1.47  tff(c_255, plain, (![A_114, B_115, C_116]: (k9_subset_1(u1_struct_0(A_114), B_115, k2_pre_topc(A_114, C_116))=C_116 | ~r1_tarski(C_116, B_115) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_114))) | ~v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.47  tff(c_259, plain, (![B_115]: (k9_subset_1(u1_struct_0('#skF_2'), B_115, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_115) | ~v2_tex_2(B_115, '#skF_2') | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_146, c_255])).
% 2.84/1.47  tff(c_268, plain, (![B_115]: (k9_subset_1(u1_struct_0('#skF_2'), B_115, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_115) | ~v2_tex_2(B_115, '#skF_2') | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_259])).
% 2.84/1.47  tff(c_306, plain, (![B_120]: (k9_subset_1(u1_struct_0('#skF_2'), B_120, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_120) | ~v2_tex_2(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_268])).
% 2.84/1.47  tff(c_36, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.84/1.47  tff(c_102, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_101, c_36])).
% 2.84/1.47  tff(c_312, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_102])).
% 2.84/1.47  tff(c_319, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_312])).
% 2.84/1.47  tff(c_323, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_125, c_319])).
% 2.84/1.47  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_323])).
% 2.84/1.47  tff(c_328, plain, (![A_69]: (~r2_hidden(A_69, '#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 2.84/1.47  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_38])).
% 2.84/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.47  
% 2.84/1.47  Inference rules
% 2.84/1.47  ----------------------
% 2.84/1.47  #Ref     : 0
% 2.84/1.47  #Sup     : 58
% 2.84/1.47  #Fact    : 0
% 2.84/1.47  #Define  : 0
% 2.84/1.47  #Split   : 5
% 2.84/1.47  #Chain   : 0
% 2.84/1.47  #Close   : 0
% 2.84/1.47  
% 2.84/1.47  Ordering : KBO
% 2.84/1.47  
% 2.84/1.47  Simplification rules
% 2.84/1.47  ----------------------
% 2.84/1.47  #Subsume      : 2
% 2.84/1.47  #Demod        : 28
% 2.84/1.47  #Tautology    : 29
% 2.84/1.47  #SimpNegUnit  : 11
% 2.84/1.47  #BackRed      : 2
% 2.84/1.47  
% 2.84/1.47  #Partial instantiations: 0
% 2.84/1.47  #Strategies tried      : 1
% 2.84/1.47  
% 2.84/1.47  Timing (in seconds)
% 2.84/1.47  ----------------------
% 2.84/1.47  Preprocessing        : 0.38
% 2.84/1.47  Parsing              : 0.19
% 2.84/1.47  CNF conversion       : 0.03
% 2.84/1.47  Main loop            : 0.25
% 2.84/1.47  Inferencing          : 0.10
% 2.84/1.47  Reduction            : 0.07
% 2.84/1.47  Demodulation         : 0.05
% 2.84/1.47  BG Simplification    : 0.02
% 2.84/1.47  Subsumption          : 0.04
% 2.84/1.47  Abstraction          : 0.02
% 2.84/1.47  MUC search           : 0.00
% 2.84/1.47  Cooper               : 0.00
% 2.84/1.47  Total                : 0.67
% 2.84/1.47  Index Insertion      : 0.00
% 2.84/1.47  Index Deletion       : 0.00
% 2.84/1.47  Index Matching       : 0.00
% 2.84/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
