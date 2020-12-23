%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 141 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 416 expanded)
%              Number of equality atoms :   10 (  51 expanded)
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_36,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_52,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tarski(A_3),k1_zfmisc_1(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_68,B_69,C_70] :
      ( k9_subset_1(u1_struct_0(A_68),B_69,k2_pre_topc(A_68,C_70)) = C_70
      | ~ r1_tarski(C_70,B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_203,plain,(
    ! [A_74,B_75,A_76] :
      ( k9_subset_1(u1_struct_0(A_74),B_75,k2_pre_topc(A_74,k1_tarski(A_76))) = k1_tarski(A_76)
      | ~ r1_tarski(k1_tarski(A_76),B_75)
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74)
      | ~ r2_hidden(A_76,u1_struct_0(A_74)) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_53,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_67,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_62])).

tff(c_22,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_22])).

tff(c_209,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_68])).

tff(c_216,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_209])).

tff(c_217,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_216])).

tff(c_219,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_222,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_219])).

tff(c_225,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_225])).

tff(c_228,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_232,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_232])).

tff(c_237,plain,(
    ! [A_36] : ~ r2_hidden(A_36,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.34  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.34  
% 2.24/1.34  %Foreground sorts:
% 2.24/1.34  
% 2.24/1.34  
% 2.24/1.34  %Background operators:
% 2.24/1.34  
% 2.24/1.34  
% 2.24/1.34  %Foreground operators:
% 2.24/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.24/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.34  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.24/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.24/1.34  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.24/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.34  
% 2.24/1.35  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.24/1.35  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.24/1.35  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.24/1.35  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.24/1.35  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.24/1.35  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.24/1.35  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.24/1.35  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.35  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_45, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.35  tff(c_51, plain, (![A_36]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_36, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.24/1.35  tff(c_52, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_51])).
% 2.24/1.35  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.35  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k1_tarski(A_3), k1_zfmisc_1(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.35  tff(c_150, plain, (![A_68, B_69, C_70]: (k9_subset_1(u1_struct_0(A_68), B_69, k2_pre_topc(A_68, C_70))=C_70 | ~r1_tarski(C_70, B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.24/1.35  tff(c_203, plain, (![A_74, B_75, A_76]: (k9_subset_1(u1_struct_0(A_74), B_75, k2_pre_topc(A_74, k1_tarski(A_76)))=k1_tarski(A_76) | ~r1_tarski(k1_tarski(A_76), B_75) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74) | ~r2_hidden(A_76, u1_struct_0(A_74)))), inference(resolution, [status(thm)], [c_6, c_150])).
% 2.24/1.35  tff(c_53, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.35  tff(c_62, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.24/1.35  tff(c_67, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_62])).
% 2.24/1.35  tff(c_22, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.24/1.35  tff(c_68, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_22])).
% 2.24/1.35  tff(c_209, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_68])).
% 2.24/1.35  tff(c_216, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_209])).
% 2.24/1.35  tff(c_217, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_216])).
% 2.24/1.35  tff(c_219, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_217])).
% 2.24/1.35  tff(c_222, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_219])).
% 2.24/1.35  tff(c_225, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_222])).
% 2.24/1.35  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_225])).
% 2.24/1.35  tff(c_228, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_217])).
% 2.24/1.35  tff(c_232, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_228])).
% 2.24/1.35  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_232])).
% 2.24/1.35  tff(c_237, plain, (![A_36]: (~r2_hidden(A_36, '#skF_3'))), inference(splitRight, [status(thm)], [c_51])).
% 2.24/1.35  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_24])).
% 2.24/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.35  
% 2.24/1.35  Inference rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Ref     : 0
% 2.24/1.35  #Sup     : 39
% 2.24/1.35  #Fact    : 0
% 2.24/1.35  #Define  : 0
% 2.24/1.35  #Split   : 5
% 2.24/1.35  #Chain   : 0
% 2.24/1.35  #Close   : 0
% 2.24/1.35  
% 2.24/1.35  Ordering : KBO
% 2.24/1.35  
% 2.24/1.35  Simplification rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Subsume      : 1
% 2.24/1.35  #Demod        : 19
% 2.24/1.35  #Tautology    : 15
% 2.24/1.35  #SimpNegUnit  : 8
% 2.24/1.35  #BackRed      : 2
% 2.24/1.35  
% 2.24/1.35  #Partial instantiations: 0
% 2.24/1.35  #Strategies tried      : 1
% 2.24/1.35  
% 2.24/1.35  Timing (in seconds)
% 2.24/1.35  ----------------------
% 2.24/1.35  Preprocessing        : 0.32
% 2.24/1.35  Parsing              : 0.17
% 2.24/1.35  CNF conversion       : 0.02
% 2.24/1.35  Main loop            : 0.23
% 2.24/1.35  Inferencing          : 0.09
% 2.24/1.35  Reduction            : 0.06
% 2.24/1.35  Demodulation         : 0.04
% 2.24/1.35  BG Simplification    : 0.01
% 2.24/1.35  Subsumption          : 0.04
% 2.24/1.36  Abstraction          : 0.01
% 2.24/1.36  MUC search           : 0.00
% 2.24/1.36  Cooper               : 0.00
% 2.24/1.36  Total                : 0.58
% 2.24/1.36  Index Insertion      : 0.00
% 2.24/1.36  Index Deletion       : 0.00
% 2.24/1.36  Index Matching       : 0.00
% 2.24/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
