%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:38 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 126 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_179,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_188,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_179])).

tff(c_193,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_188])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_194,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_48])).

tff(c_219,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k6_domain_1(A_84,B_85),k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_233,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_219])).

tff(c_239,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_233])).

tff(c_240,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_239])).

tff(c_447,plain,(
    ! [B_92,A_93] :
      ( ~ v1_subset_1(B_92,A_93)
      | v1_xboole_0(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_zfmisc_1(A_93)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_453,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_447])).

tff(c_468,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_194,c_453])).

tff(c_469,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_468])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_95,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_479,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_469,c_98])).

tff(c_55,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_73,plain,(
    ! [B_38,A_39] :
      ( ~ r1_tarski(B_38,A_39)
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ! [A_34] : ~ r1_tarski(k1_tarski(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_61,c_73])).

tff(c_499,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_84])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.61/1.34  
% 2.61/1.34  %Foreground sorts:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Background operators:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Foreground operators:
% 2.61/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.34  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.61/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.61/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.61/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.61/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.34  
% 2.61/1.36  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.61/1.36  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.36  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.61/1.36  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.61/1.36  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.61/1.36  tff(f_100, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.61/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.61/1.36  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.61/1.36  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.36  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.61/1.36  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.61/1.36  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.36  tff(c_99, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.36  tff(c_103, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.61/1.36  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.36  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.36  tff(c_50, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.36  tff(c_179, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.61/1.36  tff(c_188, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_179])).
% 2.61/1.36  tff(c_193, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_188])).
% 2.61/1.36  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.61/1.36  tff(c_194, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_48])).
% 2.61/1.36  tff(c_219, plain, (![A_84, B_85]: (m1_subset_1(k6_domain_1(A_84, B_85), k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.36  tff(c_233, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193, c_219])).
% 2.61/1.36  tff(c_239, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_233])).
% 2.61/1.36  tff(c_240, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_239])).
% 2.61/1.36  tff(c_447, plain, (![B_92, A_93]: (~v1_subset_1(B_92, A_93) | v1_xboole_0(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_zfmisc_1(A_93) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.36  tff(c_453, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_240, c_447])).
% 2.61/1.36  tff(c_468, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_194, c_453])).
% 2.61/1.36  tff(c_469, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_468])).
% 2.61/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.61/1.36  tff(c_95, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.61/1.36  tff(c_98, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_95])).
% 2.61/1.36  tff(c_479, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_469, c_98])).
% 2.61/1.36  tff(c_55, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.36  tff(c_10, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.36  tff(c_61, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_10])).
% 2.61/1.36  tff(c_73, plain, (![B_38, A_39]: (~r1_tarski(B_38, A_39) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.36  tff(c_84, plain, (![A_34]: (~r1_tarski(k1_tarski(A_34), A_34))), inference(resolution, [status(thm)], [c_61, c_73])).
% 2.61/1.36  tff(c_499, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_479, c_84])).
% 2.61/1.36  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_499])).
% 2.61/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  Inference rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Ref     : 0
% 2.61/1.36  #Sup     : 102
% 2.61/1.36  #Fact    : 0
% 2.61/1.36  #Define  : 0
% 2.61/1.36  #Split   : 1
% 2.61/1.36  #Chain   : 0
% 2.61/1.36  #Close   : 0
% 2.61/1.36  
% 2.61/1.36  Ordering : KBO
% 2.61/1.36  
% 2.61/1.36  Simplification rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Subsume      : 13
% 2.61/1.36  #Demod        : 43
% 2.61/1.36  #Tautology    : 33
% 2.61/1.36  #SimpNegUnit  : 7
% 2.61/1.36  #BackRed      : 15
% 2.61/1.36  
% 2.61/1.36  #Partial instantiations: 0
% 2.61/1.36  #Strategies tried      : 1
% 2.61/1.36  
% 2.61/1.36  Timing (in seconds)
% 2.61/1.36  ----------------------
% 2.61/1.36  Preprocessing        : 0.33
% 2.61/1.36  Parsing              : 0.18
% 2.61/1.36  CNF conversion       : 0.02
% 2.61/1.36  Main loop            : 0.27
% 2.61/1.36  Inferencing          : 0.10
% 2.61/1.36  Reduction            : 0.08
% 2.61/1.36  Demodulation         : 0.06
% 2.61/1.36  BG Simplification    : 0.02
% 2.61/1.36  Subsumption          : 0.05
% 2.61/1.36  Abstraction          : 0.02
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.63
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
