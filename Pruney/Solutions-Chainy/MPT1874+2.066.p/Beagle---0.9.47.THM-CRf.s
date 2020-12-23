%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 146 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 429 expanded)
%              Number of equality atoms :   13 (  57 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_92,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_76,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_168,plain,(
    ! [A_72,B_73,C_74] :
      ( k9_subset_1(u1_struct_0(A_72),B_73,k2_pre_topc(A_72,C_74)) = C_74
      | ~ r1_tarski(C_74,B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_234,plain,(
    ! [A_83,B_84,A_85] :
      ( k9_subset_1(u1_struct_0(A_83),B_84,k2_pre_topc(A_83,A_85)) = A_85
      | ~ r1_tarski(A_85,B_84)
      | ~ v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | ~ r1_tarski(A_85,u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_10,c_168])).

tff(c_241,plain,(
    ! [A_85] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_85)) = A_85
      | ~ r1_tarski(A_85,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_85,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_234])).

tff(c_246,plain,(
    ! [A_85] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_85)) = A_85
      | ~ r1_tarski(A_85,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_85,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_241])).

tff(c_265,plain,(
    ! [A_88] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_88)) = A_88
      | ~ r1_tarski(A_88,'#skF_3')
      | ~ r1_tarski(A_88,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_246])).

tff(c_63,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_89,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_75])).

tff(c_24,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_24])).

tff(c_294,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_90])).

tff(c_298,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_302,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_298])).

tff(c_305,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_302])).

tff(c_308,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_308])).

tff(c_311,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_315,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_311])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_320,plain,(
    ! [A_38] : ~ r2_hidden(A_38,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:17:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.39  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.56/1.39  
% 2.56/1.39  %Foreground sorts:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Background operators:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Foreground operators:
% 2.56/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.56/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.56/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.56/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.56/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.39  
% 2.56/1.40  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.56/1.40  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.56/1.40  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.56/1.40  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.56/1.40  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.40  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.56/1.40  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.56/1.40  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.40  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_56, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.40  tff(c_62, plain, (![A_38]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_56])).
% 2.56/1.40  tff(c_76, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 2.56/1.40  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.40  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_30, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.40  tff(c_168, plain, (![A_72, B_73, C_74]: (k9_subset_1(u1_struct_0(A_72), B_73, k2_pre_topc(A_72, C_74))=C_74 | ~r1_tarski(C_74, B_73) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_72))) | ~v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.40  tff(c_234, plain, (![A_83, B_84, A_85]: (k9_subset_1(u1_struct_0(A_83), B_84, k2_pre_topc(A_83, A_85))=A_85 | ~r1_tarski(A_85, B_84) | ~v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83) | ~r1_tarski(A_85, u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_10, c_168])).
% 2.56/1.40  tff(c_241, plain, (![A_85]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_85))=A_85 | ~r1_tarski(A_85, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_85, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_234])).
% 2.56/1.40  tff(c_246, plain, (![A_85]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_85))=A_85 | ~r1_tarski(A_85, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_85, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_241])).
% 2.56/1.40  tff(c_265, plain, (![A_88]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_88))=A_88 | ~r1_tarski(A_88, '#skF_3') | ~r1_tarski(A_88, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_246])).
% 2.56/1.40  tff(c_63, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.40  tff(c_75, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_63])).
% 2.56/1.40  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_75])).
% 2.56/1.40  tff(c_24, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.40  tff(c_90, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_24])).
% 2.56/1.40  tff(c_294, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_265, c_90])).
% 2.56/1.40  tff(c_298, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_294])).
% 2.56/1.40  tff(c_302, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_298])).
% 2.56/1.40  tff(c_305, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_302])).
% 2.56/1.40  tff(c_308, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_305])).
% 2.56/1.40  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_308])).
% 2.56/1.40  tff(c_311, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_294])).
% 2.56/1.40  tff(c_315, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_311])).
% 2.56/1.40  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_315])).
% 2.56/1.40  tff(c_320, plain, (![A_38]: (~r2_hidden(A_38, '#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 2.56/1.40  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_26])).
% 2.56/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.40  
% 2.56/1.40  Inference rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Ref     : 0
% 2.56/1.40  #Sup     : 58
% 2.56/1.40  #Fact    : 0
% 2.56/1.40  #Define  : 0
% 2.56/1.40  #Split   : 4
% 2.56/1.40  #Chain   : 0
% 2.56/1.40  #Close   : 0
% 2.56/1.40  
% 2.56/1.40  Ordering : KBO
% 2.56/1.40  
% 2.56/1.40  Simplification rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Subsume      : 6
% 2.56/1.40  #Demod        : 28
% 2.56/1.40  #Tautology    : 20
% 2.56/1.40  #SimpNegUnit  : 9
% 2.56/1.40  #BackRed      : 2
% 2.56/1.40  
% 2.56/1.40  #Partial instantiations: 0
% 2.56/1.40  #Strategies tried      : 1
% 2.56/1.40  
% 2.56/1.40  Timing (in seconds)
% 2.56/1.40  ----------------------
% 2.56/1.40  Preprocessing        : 0.33
% 2.56/1.40  Parsing              : 0.17
% 2.56/1.40  CNF conversion       : 0.02
% 2.56/1.40  Main loop            : 0.27
% 2.56/1.40  Inferencing          : 0.11
% 2.56/1.40  Reduction            : 0.07
% 2.56/1.40  Demodulation         : 0.04
% 2.56/1.40  BG Simplification    : 0.02
% 2.56/1.40  Subsumption          : 0.05
% 2.56/1.41  Abstraction          : 0.02
% 2.56/1.41  MUC search           : 0.00
% 2.56/1.41  Cooper               : 0.00
% 2.56/1.41  Total                : 0.63
% 2.56/1.41  Index Insertion      : 0.00
% 2.56/1.41  Index Deletion       : 0.00
% 2.56/1.41  Index Matching       : 0.00
% 2.56/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
