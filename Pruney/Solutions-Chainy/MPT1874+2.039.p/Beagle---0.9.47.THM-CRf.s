%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 128 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 367 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_103,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_83,axiom,(
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

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_80,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_16])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_83])).

tff(c_89,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_89])).

tff(c_95,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tarski(A_7),k1_zfmisc_1(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [A_58,B_59,C_60] :
      ( k9_subset_1(u1_struct_0(A_58),B_59,k2_pre_topc(A_58,C_60)) = C_60
      | ~ r1_tarski(C_60,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ v2_tex_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_176,plain,(
    ! [A_62,B_63,A_64] :
      ( k9_subset_1(u1_struct_0(A_62),B_63,k2_pre_topc(A_62,k1_tarski(A_64))) = k1_tarski(A_64)
      | ~ r1_tarski(k1_tarski(A_64),B_63)
      | ~ v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62)
      | ~ r2_hidden(A_64,u1_struct_0(A_62)) ) ),
    inference(resolution,[status(thm)],[c_10,c_142])).

tff(c_94,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_101,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_28])).

tff(c_182,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_101])).

tff(c_189,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_182])).

tff(c_190,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_189])).

tff(c_192,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_195,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_198,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_198])).

tff(c_201,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_205,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.37  
% 2.27/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.37  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.27/1.37  
% 2.27/1.37  %Foreground sorts:
% 2.27/1.37  
% 2.27/1.37  
% 2.27/1.37  %Background operators:
% 2.27/1.37  
% 2.27/1.37  
% 2.27/1.37  %Foreground operators:
% 2.27/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.27/1.37  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.27/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.27/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.27/1.37  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.27/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.37  
% 2.27/1.39  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.27/1.39  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.27/1.39  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.27/1.39  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.27/1.39  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.27/1.39  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.27/1.39  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.27/1.39  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.27/1.39  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.39  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.39  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_67, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.39  tff(c_79, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_67])).
% 2.27/1.39  tff(c_80, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_79])).
% 2.27/1.39  tff(c_16, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.39  tff(c_83, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_16])).
% 2.27/1.39  tff(c_86, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_83])).
% 2.27/1.39  tff(c_89, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_86])).
% 2.27/1.39  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_89])).
% 2.27/1.39  tff(c_95, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_79])).
% 2.27/1.39  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.39  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k1_tarski(A_7), k1_zfmisc_1(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.39  tff(c_142, plain, (![A_58, B_59, C_60]: (k9_subset_1(u1_struct_0(A_58), B_59, k2_pre_topc(A_58, C_60))=C_60 | ~r1_tarski(C_60, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_58))) | ~v2_tex_2(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.39  tff(c_176, plain, (![A_62, B_63, A_64]: (k9_subset_1(u1_struct_0(A_62), B_63, k2_pre_topc(A_62, k1_tarski(A_64)))=k1_tarski(A_64) | ~r1_tarski(k1_tarski(A_64), B_63) | ~v2_tex_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62) | ~r2_hidden(A_64, u1_struct_0(A_62)))), inference(resolution, [status(thm)], [c_10, c_142])).
% 2.27/1.39  tff(c_94, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_79])).
% 2.27/1.39  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.27/1.39  tff(c_101, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_28])).
% 2.27/1.39  tff(c_182, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_101])).
% 2.27/1.39  tff(c_189, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_182])).
% 2.27/1.39  tff(c_190, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_189])).
% 2.27/1.39  tff(c_192, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_190])).
% 2.27/1.39  tff(c_195, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_192])).
% 2.27/1.39  tff(c_198, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_195])).
% 2.27/1.39  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_198])).
% 2.27/1.39  tff(c_201, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_190])).
% 2.27/1.39  tff(c_205, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_201])).
% 2.27/1.39  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_205])).
% 2.27/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.39  
% 2.27/1.39  Inference rules
% 2.27/1.39  ----------------------
% 2.27/1.39  #Ref     : 0
% 2.27/1.39  #Sup     : 30
% 2.27/1.39  #Fact    : 0
% 2.27/1.39  #Define  : 0
% 2.27/1.39  #Split   : 3
% 2.27/1.39  #Chain   : 0
% 2.27/1.39  #Close   : 0
% 2.27/1.39  
% 2.27/1.39  Ordering : KBO
% 2.27/1.39  
% 2.27/1.39  Simplification rules
% 2.27/1.39  ----------------------
% 2.27/1.39  #Subsume      : 0
% 2.27/1.39  #Demod        : 17
% 2.27/1.39  #Tautology    : 12
% 2.27/1.39  #SimpNegUnit  : 6
% 2.27/1.39  #BackRed      : 0
% 2.27/1.39  
% 2.27/1.39  #Partial instantiations: 0
% 2.27/1.39  #Strategies tried      : 1
% 2.27/1.39  
% 2.27/1.39  Timing (in seconds)
% 2.27/1.39  ----------------------
% 2.27/1.39  Preprocessing        : 0.32
% 2.27/1.39  Parsing              : 0.17
% 2.27/1.39  CNF conversion       : 0.02
% 2.27/1.39  Main loop            : 0.20
% 2.27/1.39  Inferencing          : 0.08
% 2.27/1.39  Reduction            : 0.06
% 2.27/1.39  Demodulation         : 0.04
% 2.27/1.39  BG Simplification    : 0.01
% 2.27/1.39  Subsumption          : 0.03
% 2.27/1.39  Abstraction          : 0.01
% 2.27/1.39  MUC search           : 0.00
% 2.27/1.39  Cooper               : 0.00
% 2.27/1.39  Total                : 0.55
% 2.27/1.39  Index Insertion      : 0.00
% 2.27/1.39  Index Deletion       : 0.00
% 2.27/1.39  Index Matching       : 0.00
% 2.27/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
