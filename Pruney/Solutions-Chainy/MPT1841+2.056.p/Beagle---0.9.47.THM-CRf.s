%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:35 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_194,plain,(
    ! [A_62,B_63] :
      ( k6_domain_1(A_62,B_63) = k1_tarski(B_63)
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_197,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_194])).

tff(c_200,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_197])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_201,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_40])).

tff(c_212,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k6_domain_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_221,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_212])).

tff(c_225,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_221])).

tff(c_226,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_225])).

tff(c_242,plain,(
    ! [B_67,A_68] :
      ( ~ v1_subset_1(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_245,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_226,c_242])).

tff(c_251,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_201,c_245])).

tff(c_252,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_251])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_257,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_252,c_2])).

tff(c_22,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_tarski(A_16)) = k1_ordinal1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_268,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_ordinal1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_22])).

tff(c_271,plain,(
    k1_ordinal1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_268])).

tff(c_26,plain,(
    ! [B_18] : r2_hidden(B_18,k1_ordinal1(B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [B_34,A_35] :
      ( ~ r1_tarski(B_34,A_35)
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [B_18] : ~ r1_tarski(k1_ordinal1(B_18),B_18) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_330,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_71])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:51:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.25  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.20/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.20/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.20/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.25  
% 2.20/1.26  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.20/1.26  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.20/1.26  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.20/1.26  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.20/1.26  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.20/1.26  tff(f_94, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.20/1.26  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.20/1.26  tff(f_55, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.20/1.26  tff(f_61, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.20/1.26  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.20/1.26  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.26  tff(c_10, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.26  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.26  tff(c_38, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.26  tff(c_42, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.26  tff(c_194, plain, (![A_62, B_63]: (k6_domain_1(A_62, B_63)=k1_tarski(B_63) | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.26  tff(c_197, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_194])).
% 2.20/1.26  tff(c_200, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_197])).
% 2.20/1.26  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.20/1.26  tff(c_201, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_40])).
% 2.20/1.26  tff(c_212, plain, (![A_65, B_66]: (m1_subset_1(k6_domain_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.26  tff(c_221, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_200, c_212])).
% 2.20/1.26  tff(c_225, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_221])).
% 2.20/1.26  tff(c_226, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_225])).
% 2.20/1.26  tff(c_242, plain, (![B_67, A_68]: (~v1_subset_1(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.20/1.26  tff(c_245, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_226, c_242])).
% 2.20/1.26  tff(c_251, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_201, c_245])).
% 2.20/1.26  tff(c_252, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_251])).
% 2.20/1.26  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.26  tff(c_257, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_252, c_2])).
% 2.20/1.26  tff(c_22, plain, (![A_16]: (k2_xboole_0(A_16, k1_tarski(A_16))=k1_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.20/1.26  tff(c_268, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_ordinal1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_257, c_22])).
% 2.20/1.26  tff(c_271, plain, (k1_ordinal1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_268])).
% 2.20/1.26  tff(c_26, plain, (![B_18]: (r2_hidden(B_18, k1_ordinal1(B_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.20/1.26  tff(c_67, plain, (![B_34, A_35]: (~r1_tarski(B_34, A_35) | ~r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.26  tff(c_71, plain, (![B_18]: (~r1_tarski(k1_ordinal1(B_18), B_18))), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.20/1.26  tff(c_330, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_271, c_71])).
% 2.20/1.26  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_330])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 66
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 1
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 3
% 2.20/1.26  #Demod        : 37
% 2.20/1.26  #Tautology    : 32
% 2.20/1.26  #SimpNegUnit  : 5
% 2.20/1.26  #BackRed      : 6
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.26  Preprocessing        : 0.30
% 2.20/1.26  Parsing              : 0.16
% 2.20/1.26  CNF conversion       : 0.02
% 2.20/1.26  Main loop            : 0.20
% 2.20/1.26  Inferencing          : 0.07
% 2.20/1.26  Reduction            : 0.07
% 2.20/1.26  Demodulation         : 0.05
% 2.20/1.26  BG Simplification    : 0.01
% 2.20/1.26  Subsumption          : 0.03
% 2.20/1.26  Abstraction          : 0.01
% 2.20/1.26  MUC search           : 0.00
% 2.20/1.26  Cooper               : 0.00
% 2.20/1.26  Total                : 0.53
% 2.20/1.26  Index Insertion      : 0.00
% 2.20/1.26  Index Deletion       : 0.00
% 2.20/1.26  Index Matching       : 0.00
% 2.20/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
