%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:37 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 113 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k3_mcart_1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_50,B_51] : k2_xboole_0(k1_tarski(A_50),B_51) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_50] : k1_tarski(A_50) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_150,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_153,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_150])).

tff(c_156,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_153])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_157,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_38])).

tff(c_170,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k6_domain_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_179,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_170])).

tff(c_183,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_179])).

tff(c_184,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_183])).

tff(c_289,plain,(
    ! [B_96,A_97] :
      ( ~ v1_subset_1(B_96,A_97)
      | v1_xboole_0(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97))
      | ~ v1_zfmisc_1(A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_295,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_289])).

tff(c_304,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_157,c_295])).

tff(c_305,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_304])).

tff(c_82,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2'(A_54),A_54)
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(A_54)
      | k1_xboole_0 = A_54 ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_309,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_305,c_86])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k3_mcart_1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.20/1.26  
% 2.20/1.26  %Foreground sorts:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Background operators:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Foreground operators:
% 2.20/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.20/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.26  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.20/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.20/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.20/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.20/1.26  
% 2.20/1.27  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.20/1.27  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.20/1.27  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.20/1.27  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.20/1.27  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.20/1.27  tff(f_100, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.20/1.27  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.20/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.27  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.27  tff(c_71, plain, (![A_50, B_51]: (k2_xboole_0(k1_tarski(A_50), B_51)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.27  tff(c_75, plain, (![A_50]: (k1_tarski(A_50)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_71])).
% 2.20/1.27  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.27  tff(c_36, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.27  tff(c_40, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.27  tff(c_150, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.27  tff(c_153, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_150])).
% 2.20/1.27  tff(c_156, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_153])).
% 2.20/1.27  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.20/1.27  tff(c_157, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_38])).
% 2.20/1.27  tff(c_170, plain, (![A_77, B_78]: (m1_subset_1(k6_domain_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.27  tff(c_179, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_156, c_170])).
% 2.20/1.27  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_179])).
% 2.20/1.27  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_183])).
% 2.20/1.27  tff(c_289, plain, (![B_96, A_97]: (~v1_subset_1(B_96, A_97) | v1_xboole_0(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)) | ~v1_zfmisc_1(A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.27  tff(c_295, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_184, c_289])).
% 2.20/1.27  tff(c_304, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_157, c_295])).
% 2.20/1.27  tff(c_305, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_304])).
% 2.20/1.27  tff(c_82, plain, (![A_54]: (r2_hidden('#skF_2'(A_54), A_54) | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.27  tff(c_86, plain, (![A_54]: (~v1_xboole_0(A_54) | k1_xboole_0=A_54)), inference(resolution, [status(thm)], [c_82, c_2])).
% 2.20/1.27  tff(c_309, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_305, c_86])).
% 2.20/1.27  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_309])).
% 2.20/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  Inference rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Ref     : 0
% 2.20/1.27  #Sup     : 57
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
% 2.20/1.27  #Subsume      : 3
% 2.20/1.27  #Demod        : 15
% 2.20/1.27  #Tautology    : 30
% 2.20/1.27  #SimpNegUnit  : 9
% 2.20/1.27  #BackRed      : 3
% 2.20/1.27  
% 2.20/1.27  #Partial instantiations: 0
% 2.20/1.27  #Strategies tried      : 1
% 2.20/1.27  
% 2.20/1.27  Timing (in seconds)
% 2.20/1.27  ----------------------
% 2.20/1.27  Preprocessing        : 0.31
% 2.20/1.27  Parsing              : 0.17
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.20
% 2.20/1.27  Inferencing          : 0.08
% 2.20/1.27  Reduction            : 0.06
% 2.20/1.27  Demodulation         : 0.04
% 2.20/1.27  BG Simplification    : 0.01
% 2.20/1.27  Subsumption          : 0.03
% 2.20/1.27  Abstraction          : 0.01
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.54
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
