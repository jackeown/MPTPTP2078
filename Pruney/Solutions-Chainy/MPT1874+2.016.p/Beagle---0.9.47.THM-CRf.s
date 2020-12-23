%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:39 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 118 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 305 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_98,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_78,axiom,(
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

tff(f_30,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_71,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k1_tarski(A_36),k1_zfmisc_1(B_37))
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_71,c_10])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_61,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_70,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_87,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_87])).

tff(c_105,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_99])).

tff(c_123,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k6_domain_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_135,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_123])).

tff(c_140,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_135])).

tff(c_141,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_140])).

tff(c_370,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(u1_struct_0(A_74),B_75,k2_pre_topc(A_74,C_76)) = C_76
      | ~ r1_tarski(C_76,B_75)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_374,plain,(
    ! [B_75] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_75,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_75)
      | ~ v2_tex_2(B_75,'#skF_2')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_141,c_370])).

tff(c_389,plain,(
    ! [B_75] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_75,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_75)
      | ~ v2_tex_2(B_75,'#skF_2')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_374])).

tff(c_437,plain,(
    ! [B_78] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_78,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_78)
      | ~ v2_tex_2(B_78,'#skF_2')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_389])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_106,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_105,c_26])).

tff(c_443,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_106])).

tff(c_450,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_443])).

tff(c_454,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_450])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_454])).

tff(c_459,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_468,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k1_tarski(A_81),k1_zfmisc_1(B_82))
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_471,plain,(
    ! [A_81,B_82] :
      ( v1_xboole_0(k1_tarski(A_81))
      | ~ v1_xboole_0(B_82)
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_468,c_8])).

tff(c_497,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_471])).

tff(c_500,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_497])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.52  
% 2.86/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.52  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.86/1.52  
% 2.86/1.52  %Foreground sorts:
% 2.86/1.52  
% 2.86/1.52  
% 2.86/1.52  %Background operators:
% 2.86/1.52  
% 2.86/1.52  
% 2.86/1.52  %Foreground operators:
% 2.86/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.86/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.86/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.86/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.52  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.86/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.86/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.86/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.86/1.52  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.86/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.52  
% 2.86/1.53  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.86/1.53  tff(f_34, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.86/1.53  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.53  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.86/1.53  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.86/1.53  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.86/1.53  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.86/1.53  tff(f_30, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.86/1.53  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_71, plain, (![A_36, B_37]: (m1_subset_1(k1_tarski(A_36), k1_zfmisc_1(B_37)) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.53  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.53  tff(c_81, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(resolution, [status(thm)], [c_71, c_10])).
% 2.86/1.53  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_32, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_61, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.53  tff(c_69, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.86/1.53  tff(c_70, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_69])).
% 2.86/1.53  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_87, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.53  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_87])).
% 2.86/1.53  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_99])).
% 2.86/1.53  tff(c_123, plain, (![A_46, B_47]: (m1_subset_1(k6_domain_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.53  tff(c_135, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_123])).
% 2.86/1.53  tff(c_140, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_135])).
% 2.86/1.53  tff(c_141, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_70, c_140])).
% 2.86/1.53  tff(c_370, plain, (![A_74, B_75, C_76]: (k9_subset_1(u1_struct_0(A_74), B_75, k2_pre_topc(A_74, C_76))=C_76 | ~r1_tarski(C_76, B_75) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_74))) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.53  tff(c_374, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_2'), B_75, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_75) | ~v2_tex_2(B_75, '#skF_2') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_141, c_370])).
% 2.86/1.53  tff(c_389, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_2'), B_75, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_75) | ~v2_tex_2(B_75, '#skF_2') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_374])).
% 2.86/1.53  tff(c_437, plain, (![B_78]: (k9_subset_1(u1_struct_0('#skF_2'), B_78, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_78) | ~v2_tex_2(B_78, '#skF_2') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_389])).
% 2.86/1.53  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.53  tff(c_106, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_105, c_26])).
% 2.86/1.53  tff(c_443, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_437, c_106])).
% 2.86/1.53  tff(c_450, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_443])).
% 2.86/1.53  tff(c_454, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_81, c_450])).
% 2.86/1.53  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_454])).
% 2.86/1.53  tff(c_459, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_69])).
% 2.86/1.53  tff(c_4, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.86/1.53  tff(c_468, plain, (![A_81, B_82]: (m1_subset_1(k1_tarski(A_81), k1_zfmisc_1(B_82)) | ~r2_hidden(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.53  tff(c_8, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.53  tff(c_471, plain, (![A_81, B_82]: (v1_xboole_0(k1_tarski(A_81)) | ~v1_xboole_0(B_82) | ~r2_hidden(A_81, B_82))), inference(resolution, [status(thm)], [c_468, c_8])).
% 2.86/1.53  tff(c_497, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r2_hidden(A_86, B_85))), inference(negUnitSimplification, [status(thm)], [c_4, c_471])).
% 2.86/1.53  tff(c_500, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_497])).
% 2.86/1.53  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_500])).
% 2.86/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.53  
% 2.86/1.53  Inference rules
% 2.86/1.53  ----------------------
% 2.86/1.53  #Ref     : 0
% 2.86/1.53  #Sup     : 94
% 2.86/1.53  #Fact    : 0
% 2.86/1.53  #Define  : 0
% 2.86/1.54  #Split   : 4
% 2.86/1.54  #Chain   : 0
% 2.86/1.54  #Close   : 0
% 2.86/1.54  
% 2.86/1.54  Ordering : KBO
% 2.86/1.54  
% 2.86/1.54  Simplification rules
% 2.86/1.54  ----------------------
% 2.86/1.54  #Subsume      : 8
% 2.86/1.54  #Demod        : 35
% 2.86/1.54  #Tautology    : 28
% 2.86/1.54  #SimpNegUnit  : 21
% 2.86/1.54  #BackRed      : 1
% 2.86/1.54  
% 2.86/1.54  #Partial instantiations: 0
% 2.86/1.54  #Strategies tried      : 1
% 2.86/1.54  
% 2.86/1.54  Timing (in seconds)
% 2.86/1.54  ----------------------
% 2.86/1.54  Preprocessing        : 0.29
% 2.86/1.54  Parsing              : 0.15
% 2.86/1.54  CNF conversion       : 0.02
% 2.86/1.54  Main loop            : 0.38
% 2.86/1.54  Inferencing          : 0.14
% 2.86/1.54  Reduction            : 0.11
% 2.86/1.54  Demodulation         : 0.06
% 2.86/1.54  BG Simplification    : 0.02
% 2.86/1.54  Subsumption          : 0.07
% 2.86/1.54  Abstraction          : 0.02
% 2.86/1.54  MUC search           : 0.00
% 2.86/1.54  Cooper               : 0.00
% 2.86/1.54  Total                : 0.70
% 2.86/1.54  Index Insertion      : 0.00
% 2.86/1.54  Index Deletion       : 0.00
% 2.86/1.54  Index Matching       : 0.00
% 2.86/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
