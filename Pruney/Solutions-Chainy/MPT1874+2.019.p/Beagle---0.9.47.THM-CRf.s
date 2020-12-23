%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:39 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 188 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 523 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_97,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k1_tarski(A_3),B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [B_38,A_39] :
      ( v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(k1_tarski(A_5))
      | ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_83,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_62])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_69,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_92,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_69])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_151,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(u1_struct_0(A_56),B_57,k2_pre_topc(A_56,C_58)) = C_58
      | ~ r1_tarski(C_58,B_57)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ v2_tex_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_228,plain,(
    ! [A_68,B_69,A_70] :
      ( k9_subset_1(u1_struct_0(A_68),B_69,k2_pre_topc(A_68,k1_tarski(A_70))) = k1_tarski(A_70)
      | ~ r1_tarski(k1_tarski(A_70),B_69)
      | ~ v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68)
      | ~ r2_hidden(A_70,u1_struct_0(A_68)) ) ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_70,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_93,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_82])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_94,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_26])).

tff(c_234,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_94])).

tff(c_241,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_234])).

tff(c_242,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_241])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_247,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_244])).

tff(c_250,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_250])).

tff(c_253,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_257,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_253])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.27  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.21/1.27  
% 2.21/1.27  %Foreground sorts:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Background operators:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Foreground operators:
% 2.21/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.21/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.21/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.21/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.21/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.27  
% 2.21/1.28  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.21/1.28  tff(f_34, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.21/1.28  tff(f_30, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.21/1.28  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.21/1.28  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.21/1.28  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.21/1.28  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.21/1.28  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.21/1.28  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k1_tarski(A_3), B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.28  tff(c_4, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.21/1.28  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.28  tff(c_59, plain, (![B_38, A_39]: (v1_xboole_0(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.28  tff(c_62, plain, (![A_5, B_6]: (v1_xboole_0(k1_tarski(A_5)) | ~v1_xboole_0(B_6) | ~r2_hidden(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_59])).
% 2.21/1.28  tff(c_83, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | ~r2_hidden(A_43, B_42))), inference(negUnitSimplification, [status(thm)], [c_4, c_62])).
% 2.21/1.28  tff(c_91, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_83])).
% 2.21/1.28  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_69, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.21/1.28  tff(c_92, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_91, c_69])).
% 2.21/1.28  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_14, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.28  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_32, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_151, plain, (![A_56, B_57, C_58]: (k9_subset_1(u1_struct_0(A_56), B_57, k2_pre_topc(A_56, C_58))=C_58 | ~r1_tarski(C_58, B_57) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_56))) | ~v2_tex_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.28  tff(c_228, plain, (![A_68, B_69, A_70]: (k9_subset_1(u1_struct_0(A_68), B_69, k2_pre_topc(A_68, k1_tarski(A_70)))=k1_tarski(A_70) | ~r1_tarski(k1_tarski(A_70), B_69) | ~v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68) | ~r2_hidden(A_70, u1_struct_0(A_68)))), inference(resolution, [status(thm)], [c_10, c_151])).
% 2.21/1.28  tff(c_70, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.21/1.28  tff(c_82, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_70])).
% 2.21/1.28  tff(c_93, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_82])).
% 2.21/1.28  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.21/1.28  tff(c_94, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_26])).
% 2.21/1.28  tff(c_234, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_94])).
% 2.21/1.28  tff(c_241, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_234])).
% 2.21/1.28  tff(c_242, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_241])).
% 2.21/1.28  tff(c_244, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_242])).
% 2.21/1.28  tff(c_247, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_244])).
% 2.21/1.28  tff(c_250, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_247])).
% 2.21/1.28  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_250])).
% 2.21/1.28  tff(c_253, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_242])).
% 2.21/1.28  tff(c_257, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_253])).
% 2.21/1.28  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_257])).
% 2.21/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  Inference rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Ref     : 0
% 2.21/1.28  #Sup     : 42
% 2.21/1.28  #Fact    : 0
% 2.21/1.28  #Define  : 0
% 2.21/1.28  #Split   : 3
% 2.21/1.28  #Chain   : 0
% 2.21/1.28  #Close   : 0
% 2.21/1.28  
% 2.21/1.28  Ordering : KBO
% 2.21/1.28  
% 2.21/1.28  Simplification rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Subsume      : 4
% 2.21/1.28  #Demod        : 22
% 2.21/1.28  #Tautology    : 17
% 2.21/1.28  #SimpNegUnit  : 10
% 2.21/1.28  #BackRed      : 1
% 2.21/1.28  
% 2.21/1.28  #Partial instantiations: 0
% 2.21/1.28  #Strategies tried      : 1
% 2.21/1.28  
% 2.21/1.28  Timing (in seconds)
% 2.21/1.28  ----------------------
% 2.21/1.28  Preprocessing        : 0.30
% 2.21/1.28  Parsing              : 0.15
% 2.21/1.28  CNF conversion       : 0.02
% 2.21/1.28  Main loop            : 0.22
% 2.21/1.28  Inferencing          : 0.09
% 2.21/1.28  Reduction            : 0.06
% 2.21/1.28  Demodulation         : 0.04
% 2.21/1.28  BG Simplification    : 0.01
% 2.21/1.28  Subsumption          : 0.04
% 2.21/1.28  Abstraction          : 0.01
% 2.21/1.28  MUC search           : 0.00
% 2.21/1.28  Cooper               : 0.00
% 2.21/1.29  Total                : 0.55
% 2.21/1.29  Index Insertion      : 0.00
% 2.21/1.29  Index Deletion       : 0.00
% 2.21/1.29  Index Matching       : 0.00
% 2.21/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
