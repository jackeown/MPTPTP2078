%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 173 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 371 expanded)
%              Number of equality atoms :   16 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_39,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_43,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_45,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_32])).

tff(c_58,plain,(
    ! [B_22,A_23] :
      ( v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_45,c_58])).

tff(c_67,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    ! [A_24] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v7_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_68])).

tff(c_73,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_2'))
    | v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_74,plain,(
    ~ v1_zfmisc_1(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_73])).

tff(c_123,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_45,c_123])).

tff(c_140,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_132])).

tff(c_148,plain,(
    ! [A_43,B_44] :
      ( v1_zfmisc_1(A_43)
      | k6_domain_1(A_43,B_44) != A_43
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_157,plain,
    ( v1_zfmisc_1(k2_struct_0('#skF_2'))
    | k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_45,c_148])).

tff(c_164,plain,
    ( v1_zfmisc_1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') != k1_tarski('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_157])).

tff(c_165,plain,(
    k2_struct_0('#skF_2') != k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_74,c_164])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_tarski(A_3),k1_zfmisc_1(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [B_33,A_34] :
      ( v1_subset_1(B_33,A_34)
      | B_33 = A_34
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_167,plain,(
    ! [A_45,B_46] :
      ( v1_subset_1(k1_tarski(A_45),B_46)
      | k1_tarski(A_45) = B_46
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_30,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_51,plain,(
    ~ v1_subset_1(k6_domain_1(k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_43,c_30])).

tff(c_142,plain,(
    ~ v1_subset_1(k1_tarski('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_51])).

tff(c_170,plain,
    ( k2_struct_0('#skF_2') = k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_167,c_142])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_170])).

tff(c_187,plain,
    ( ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_190,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_190])).

tff(c_194,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_14,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_197,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_194,c_14])).

tff(c_200,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.10/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.25  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.10/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.10/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.10/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.25  
% 2.20/1.27  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.20/1.27  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.20/1.27  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.20/1.27  tff(f_62, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.20/1.27  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.20/1.27  tff(f_79, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.20/1.27  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.20/1.27  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.20/1.27  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.20/1.27  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.27  tff(c_34, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.27  tff(c_39, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.27  tff(c_43, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_39])).
% 2.20/1.27  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.27  tff(c_45, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_32])).
% 2.20/1.27  tff(c_58, plain, (![B_22, A_23]: (v1_xboole_0(B_22) | ~m1_subset_1(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.27  tff(c_65, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_45, c_58])).
% 2.20/1.27  tff(c_67, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_65])).
% 2.20/1.27  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.27  tff(c_36, plain, (~v7_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.27  tff(c_68, plain, (![A_24]: (~v1_zfmisc_1(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v7_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.27  tff(c_71, plain, (~v1_zfmisc_1(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_43, c_68])).
% 2.20/1.27  tff(c_73, plain, (~v1_zfmisc_1(k2_struct_0('#skF_2')) | v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_71])).
% 2.20/1.27  tff(c_74, plain, (~v1_zfmisc_1(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_73])).
% 2.20/1.27  tff(c_123, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.27  tff(c_132, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_45, c_123])).
% 2.20/1.27  tff(c_140, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_67, c_132])).
% 2.20/1.27  tff(c_148, plain, (![A_43, B_44]: (v1_zfmisc_1(A_43) | k6_domain_1(A_43, B_44)!=A_43 | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.27  tff(c_157, plain, (v1_zfmisc_1(k2_struct_0('#skF_2')) | k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_45, c_148])).
% 2.20/1.27  tff(c_164, plain, (v1_zfmisc_1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')!=k1_tarski('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_157])).
% 2.20/1.27  tff(c_165, plain, (k2_struct_0('#skF_2')!=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_67, c_74, c_164])).
% 2.20/1.27  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(k1_tarski(A_3), k1_zfmisc_1(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.20/1.27  tff(c_97, plain, (![B_33, A_34]: (v1_subset_1(B_33, A_34) | B_33=A_34 | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.27  tff(c_167, plain, (![A_45, B_46]: (v1_subset_1(k1_tarski(A_45), B_46) | k1_tarski(A_45)=B_46 | ~r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_10, c_97])).
% 2.20/1.27  tff(c_30, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.27  tff(c_51, plain, (~v1_subset_1(k6_domain_1(k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_43, c_30])).
% 2.20/1.27  tff(c_142, plain, (~v1_subset_1(k1_tarski('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_51])).
% 2.20/1.27  tff(c_170, plain, (k2_struct_0('#skF_2')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_167, c_142])).
% 2.20/1.27  tff(c_180, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_165, c_170])).
% 2.20/1.27  tff(c_187, plain, (~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_180])).
% 2.20/1.27  tff(c_190, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_187])).
% 2.20/1.27  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_190])).
% 2.20/1.27  tff(c_194, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_65])).
% 2.20/1.27  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k2_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.20/1.27  tff(c_197, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_194, c_14])).
% 2.20/1.27  tff(c_200, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_197])).
% 2.20/1.27  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_200])).
% 2.20/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  Inference rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Ref     : 0
% 2.20/1.27  #Sup     : 31
% 2.20/1.27  #Fact    : 0
% 2.20/1.27  #Define  : 0
% 2.20/1.27  #Split   : 1
% 2.20/1.27  #Chain   : 0
% 2.20/1.27  #Close   : 0
% 2.20/1.27  
% 2.20/1.27  Ordering : KBO
% 2.20/1.27  
% 2.20/1.27  Simplification rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Subsume      : 0
% 2.20/1.27  #Demod        : 8
% 2.20/1.27  #Tautology    : 14
% 2.20/1.27  #SimpNegUnit  : 6
% 2.20/1.27  #BackRed      : 2
% 2.20/1.27  
% 2.20/1.27  #Partial instantiations: 0
% 2.20/1.27  #Strategies tried      : 1
% 2.20/1.27  
% 2.20/1.27  Timing (in seconds)
% 2.20/1.27  ----------------------
% 2.20/1.27  Preprocessing        : 0.31
% 2.20/1.27  Parsing              : 0.16
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.16
% 2.20/1.27  Inferencing          : 0.06
% 2.20/1.27  Reduction            : 0.05
% 2.20/1.27  Demodulation         : 0.03
% 2.20/1.27  BG Simplification    : 0.01
% 2.20/1.27  Subsumption          : 0.02
% 2.20/1.27  Abstraction          : 0.01
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.50
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
