%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:40 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 143 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 378 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_99,negated_conjecture,(
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
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_79,axiom,(
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

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [C_37,B_38,A_39] :
      ( ~ v1_xboole_0(C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [B_40,A_41,A_42] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_hidden(A_41,A_42)
      | ~ r1_tarski(A_42,B_40) ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_83,plain,(
    ! [B_43] :
      ( ~ v1_xboole_0(B_43)
      | ~ r1_tarski('#skF_3',B_43) ) ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_45,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_93,plain,(
    ! [A_44,B_45] :
      ( k6_domain_1(A_44,B_45) = k1_tarski(B_45)
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_93])).

tff(c_109,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_99])).

tff(c_118,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k6_domain_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_118])).

tff(c_134,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_129])).

tff(c_135,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_134])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_146,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_76,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_77,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_105,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_93])).

tff(c_113,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_105])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k6_domain_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_158,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_154])).

tff(c_159,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_158])).

tff(c_338,plain,(
    ! [A_72,B_73,C_74] :
      ( k9_subset_1(u1_struct_0(A_72),B_73,k2_pre_topc(A_72,C_74)) = C_74
      | ~ r1_tarski(C_74,B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_342,plain,(
    ! [B_73] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_73,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_73)
      | ~ v2_tex_2(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_159,c_338])).

tff(c_354,plain,(
    ! [B_73] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_73,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_73)
      | ~ v2_tex_2(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_342])).

tff(c_420,plain,(
    ! [B_77] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_77,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_77)
      | ~ v2_tex_2(B_77,'#skF_2')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_354])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_150,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_28])).

tff(c_426,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_150])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_146,c_426])).

tff(c_435,plain,(
    ! [A_39] : ~ r2_hidden(A_39,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.43/1.35  
% 2.43/1.35  %Foreground sorts:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Background operators:
% 2.43/1.35  
% 2.43/1.35  
% 2.43/1.35  %Foreground operators:
% 2.43/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.43/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.35  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.43/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.43/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.43/1.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.43/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.35  
% 2.43/1.37  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.43/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.37  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.43/1.37  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.43/1.37  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.43/1.37  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.43/1.37  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.43/1.37  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.43/1.37  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.37  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.37  tff(c_70, plain, (![C_37, B_38, A_39]: (~v1_xboole_0(C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.37  tff(c_79, plain, (![B_40, A_41, A_42]: (~v1_xboole_0(B_40) | ~r2_hidden(A_41, A_42) | ~r1_tarski(A_42, B_40))), inference(resolution, [status(thm)], [c_12, c_70])).
% 2.43/1.37  tff(c_83, plain, (![B_43]: (~v1_xboole_0(B_43) | ~r1_tarski('#skF_3', B_43))), inference(resolution, [status(thm)], [c_30, c_79])).
% 2.43/1.37  tff(c_92, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_83])).
% 2.43/1.37  tff(c_45, plain, (![A_29, B_30]: (m1_subset_1(A_29, B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.37  tff(c_49, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.43/1.37  tff(c_93, plain, (![A_44, B_45]: (k6_domain_1(A_44, B_45)=k1_tarski(B_45) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.37  tff(c_99, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_49, c_93])).
% 2.43/1.37  tff(c_109, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_99])).
% 2.43/1.37  tff(c_118, plain, (![A_46, B_47]: (m1_subset_1(k6_domain_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.37  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_118])).
% 2.43/1.37  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_129])).
% 2.43/1.37  tff(c_135, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_134])).
% 2.43/1.37  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.37  tff(c_146, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_135, c_10])).
% 2.43/1.37  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_76, plain, (![A_39]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_70])).
% 2.43/1.37  tff(c_77, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_76])).
% 2.43/1.37  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_93])).
% 2.43/1.37  tff(c_113, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_77, c_105])).
% 2.43/1.37  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(k6_domain_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.37  tff(c_154, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 2.43/1.37  tff(c_158, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_154])).
% 2.43/1.37  tff(c_159, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_77, c_158])).
% 2.43/1.37  tff(c_338, plain, (![A_72, B_73, C_74]: (k9_subset_1(u1_struct_0(A_72), B_73, k2_pre_topc(A_72, C_74))=C_74 | ~r1_tarski(C_74, B_73) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_72))) | ~v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.37  tff(c_342, plain, (![B_73]: (k9_subset_1(u1_struct_0('#skF_2'), B_73, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_73) | ~v2_tex_2(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_159, c_338])).
% 2.43/1.37  tff(c_354, plain, (![B_73]: (k9_subset_1(u1_struct_0('#skF_2'), B_73, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_73) | ~v2_tex_2(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_342])).
% 2.43/1.37  tff(c_420, plain, (![B_77]: (k9_subset_1(u1_struct_0('#skF_2'), B_77, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_77) | ~v2_tex_2(B_77, '#skF_2') | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_354])).
% 2.43/1.37  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.43/1.37  tff(c_150, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_28])).
% 2.43/1.37  tff(c_426, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_420, c_150])).
% 2.43/1.37  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_146, c_426])).
% 2.43/1.37  tff(c_435, plain, (![A_39]: (~r2_hidden(A_39, '#skF_3'))), inference(splitRight, [status(thm)], [c_76])).
% 2.43/1.37  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_30])).
% 2.43/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.37  
% 2.43/1.37  Inference rules
% 2.43/1.37  ----------------------
% 2.43/1.37  #Ref     : 0
% 2.43/1.37  #Sup     : 86
% 2.43/1.37  #Fact    : 0
% 2.43/1.37  #Define  : 0
% 2.43/1.37  #Split   : 7
% 2.43/1.37  #Chain   : 0
% 2.43/1.37  #Close   : 0
% 2.43/1.37  
% 2.43/1.37  Ordering : KBO
% 2.43/1.37  
% 2.43/1.37  Simplification rules
% 2.43/1.37  ----------------------
% 2.43/1.37  #Subsume      : 7
% 2.43/1.37  #Demod        : 44
% 2.43/1.37  #Tautology    : 28
% 2.43/1.37  #SimpNegUnit  : 17
% 2.43/1.37  #BackRed      : 2
% 2.43/1.37  
% 2.43/1.37  #Partial instantiations: 0
% 2.43/1.37  #Strategies tried      : 1
% 2.43/1.37  
% 2.43/1.37  Timing (in seconds)
% 2.43/1.37  ----------------------
% 2.76/1.37  Preprocessing        : 0.30
% 2.76/1.37  Parsing              : 0.15
% 2.76/1.37  CNF conversion       : 0.02
% 2.76/1.37  Main loop            : 0.28
% 2.76/1.37  Inferencing          : 0.10
% 2.76/1.37  Reduction            : 0.08
% 2.76/1.37  Demodulation         : 0.06
% 2.76/1.37  BG Simplification    : 0.02
% 2.76/1.37  Subsumption          : 0.06
% 2.76/1.37  Abstraction          : 0.02
% 2.76/1.37  MUC search           : 0.00
% 2.76/1.37  Cooper               : 0.00
% 2.76/1.37  Total                : 0.61
% 2.76/1.37  Index Insertion      : 0.00
% 2.76/1.37  Index Deletion       : 0.00
% 2.76/1.37  Index Matching       : 0.00
% 2.76/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
