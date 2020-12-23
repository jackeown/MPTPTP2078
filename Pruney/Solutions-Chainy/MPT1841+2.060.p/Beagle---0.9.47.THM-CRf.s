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
% DateTime   : Thu Dec  3 10:28:36 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   58 (  75 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_152,plain,(
    ! [A_69,B_70] :
      ( k6_domain_1(A_69,B_70) = k1_tarski(B_70)
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_152])).

tff(c_158,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_155])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_159,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_48])).

tff(c_164,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_173,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_164])).

tff(c_177,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_173])).

tff(c_178,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_177])).

tff(c_384,plain,(
    ! [B_91,A_92] :
      ( ~ v1_subset_1(B_91,A_92)
      | v1_xboole_0(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_zfmisc_1(A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_390,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_384])).

tff(c_397,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_159,c_390])).

tff(c_398,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_397])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_403,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_398,c_2])).

tff(c_30,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_9,A_3,C_5] : r2_hidden(E_9,k1_enumset1(A_3,E_9,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,(
    ! [A_56,B_57] : r2_hidden(A_56,k2_tarski(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10])).

tff(c_119,plain,(
    ! [A_58] : r2_hidden(A_58,k1_tarski(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_111])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_123,plain,(
    ! [A_58] : ~ r1_tarski(k1_tarski(A_58),A_58) ),
    inference(resolution,[status(thm)],[c_119,c_38])).

tff(c_417,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_123])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:53:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.34  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.40/1.34  
% 2.40/1.34  %Foreground sorts:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Background operators:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Foreground operators:
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.34  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.40/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.40/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.40/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.40/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.40/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.34  
% 2.40/1.36  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.40/1.36  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.40/1.36  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.40/1.36  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.40/1.36  tff(f_93, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.40/1.36  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.40/1.36  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.40/1.36  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.40/1.36  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.40/1.36  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.40/1.36  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.36  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.36  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.36  tff(c_50, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.36  tff(c_152, plain, (![A_69, B_70]: (k6_domain_1(A_69, B_70)=k1_tarski(B_70) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.40/1.36  tff(c_155, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_152])).
% 2.40/1.36  tff(c_158, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_155])).
% 2.40/1.36  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.36  tff(c_159, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_48])).
% 2.40/1.36  tff(c_164, plain, (![A_71, B_72]: (m1_subset_1(k6_domain_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.40/1.36  tff(c_173, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_158, c_164])).
% 2.40/1.36  tff(c_177, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_173])).
% 2.40/1.36  tff(c_178, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_177])).
% 2.40/1.36  tff(c_384, plain, (![B_91, A_92]: (~v1_subset_1(B_91, A_92) | v1_xboole_0(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_zfmisc_1(A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.40/1.36  tff(c_390, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_178, c_384])).
% 2.40/1.36  tff(c_397, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_159, c_390])).
% 2.40/1.36  tff(c_398, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_397])).
% 2.40/1.36  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.36  tff(c_403, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_398, c_2])).
% 2.40/1.36  tff(c_30, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.36  tff(c_83, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.40/1.36  tff(c_10, plain, (![E_9, A_3, C_5]: (r2_hidden(E_9, k1_enumset1(A_3, E_9, C_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.40/1.36  tff(c_111, plain, (![A_56, B_57]: (r2_hidden(A_56, k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_10])).
% 2.40/1.36  tff(c_119, plain, (![A_58]: (r2_hidden(A_58, k1_tarski(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_111])).
% 2.40/1.36  tff(c_38, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.36  tff(c_123, plain, (![A_58]: (~r1_tarski(k1_tarski(A_58), A_58))), inference(resolution, [status(thm)], [c_119, c_38])).
% 2.40/1.36  tff(c_417, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_403, c_123])).
% 2.40/1.36  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_417])).
% 2.40/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.36  
% 2.40/1.36  Inference rules
% 2.40/1.36  ----------------------
% 2.40/1.36  #Ref     : 0
% 2.40/1.36  #Sup     : 82
% 2.40/1.36  #Fact    : 0
% 2.40/1.36  #Define  : 0
% 2.40/1.36  #Split   : 2
% 2.40/1.36  #Chain   : 0
% 2.40/1.36  #Close   : 0
% 2.40/1.36  
% 2.40/1.36  Ordering : KBO
% 2.40/1.36  
% 2.40/1.36  Simplification rules
% 2.40/1.36  ----------------------
% 2.40/1.36  #Subsume      : 9
% 2.40/1.36  #Demod        : 37
% 2.40/1.36  #Tautology    : 38
% 2.40/1.36  #SimpNegUnit  : 8
% 2.40/1.36  #BackRed      : 15
% 2.40/1.36  
% 2.40/1.36  #Partial instantiations: 0
% 2.40/1.36  #Strategies tried      : 1
% 2.40/1.36  
% 2.40/1.36  Timing (in seconds)
% 2.40/1.36  ----------------------
% 2.40/1.36  Preprocessing        : 0.33
% 2.40/1.36  Parsing              : 0.18
% 2.40/1.36  CNF conversion       : 0.02
% 2.40/1.36  Main loop            : 0.23
% 2.40/1.36  Inferencing          : 0.08
% 2.40/1.36  Reduction            : 0.07
% 2.40/1.36  Demodulation         : 0.05
% 2.40/1.36  BG Simplification    : 0.02
% 2.40/1.36  Subsumption          : 0.04
% 2.40/1.36  Abstraction          : 0.01
% 2.40/1.36  MUC search           : 0.00
% 2.40/1.36  Cooper               : 0.00
% 2.40/1.36  Total                : 0.60
% 2.40/1.36  Index Insertion      : 0.00
% 2.40/1.36  Index Deletion       : 0.00
% 2.40/1.36  Index Matching       : 0.00
% 2.40/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
