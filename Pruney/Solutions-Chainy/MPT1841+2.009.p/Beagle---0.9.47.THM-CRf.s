%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:29 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   50 (  67 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 111 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_80,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden(A_28,B_29)
      | ~ r1_xboole_0(k1_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_28] : ~ r2_hidden(A_28,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,(
    ! [A_33,B_34] :
      ( k6_domain_1(A_33,B_34) = k1_tarski(B_34)
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_69,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_66])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_70,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_32])).

tff(c_76,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k6_domain_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_76])).

tff(c_89,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_85])).

tff(c_90,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_89])).

tff(c_370,plain,(
    ! [B_58,A_59] :
      ( ~ v1_subset_1(B_58,A_59)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_zfmisc_1(A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_376,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_370])).

tff(c_383,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_70,c_376])).

tff(c_384,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_383])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_389,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_384,c_2])).

tff(c_8,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_406,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_8])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.37  
% 2.29/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.38  %$ v1_subset_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.29/1.38  
% 2.29/1.38  %Foreground sorts:
% 2.29/1.38  
% 2.29/1.38  
% 2.29/1.38  %Background operators:
% 2.29/1.38  
% 2.29/1.38  
% 2.29/1.38  %Foreground operators:
% 2.29/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.29/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.29/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.38  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.29/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.38  
% 2.55/1.39  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.55/1.39  tff(f_45, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.55/1.39  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.55/1.39  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.55/1.39  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.55/1.39  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.55/1.39  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.55/1.39  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.55/1.39  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.39  tff(c_55, plain, (![A_28, B_29]: (~r2_hidden(A_28, B_29) | ~r1_xboole_0(k1_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.39  tff(c_60, plain, (![A_28]: (~r2_hidden(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_55])).
% 2.55/1.39  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.39  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.39  tff(c_63, plain, (![A_33, B_34]: (k6_domain_1(A_33, B_34)=k1_tarski(B_34) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.55/1.39  tff(c_66, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.55/1.39  tff(c_69, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_66])).
% 2.55/1.39  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.39  tff(c_70, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_32])).
% 2.55/1.39  tff(c_76, plain, (![A_37, B_38]: (m1_subset_1(k6_domain_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.39  tff(c_85, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_69, c_76])).
% 2.55/1.39  tff(c_89, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_85])).
% 2.55/1.39  tff(c_90, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_89])).
% 2.55/1.39  tff(c_370, plain, (![B_58, A_59]: (~v1_subset_1(B_58, A_59) | v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_zfmisc_1(A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.55/1.39  tff(c_376, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_90, c_370])).
% 2.55/1.39  tff(c_383, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_70, c_376])).
% 2.55/1.39  tff(c_384, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_383])).
% 2.55/1.39  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.39  tff(c_389, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_384, c_2])).
% 2.55/1.39  tff(c_8, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.39  tff(c_406, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_389, c_8])).
% 2.55/1.39  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_406])).
% 2.55/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  Inference rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Ref     : 0
% 2.55/1.39  #Sup     : 82
% 2.55/1.39  #Fact    : 0
% 2.55/1.39  #Define  : 0
% 2.55/1.39  #Split   : 2
% 2.55/1.39  #Chain   : 0
% 2.55/1.39  #Close   : 0
% 2.55/1.39  
% 2.55/1.39  Ordering : KBO
% 2.55/1.39  
% 2.55/1.39  Simplification rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Subsume      : 11
% 2.55/1.39  #Demod        : 44
% 2.55/1.39  #Tautology    : 43
% 2.55/1.39  #SimpNegUnit  : 12
% 2.55/1.39  #BackRed      : 15
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.34
% 2.55/1.39  Parsing              : 0.17
% 2.55/1.39  CNF conversion       : 0.02
% 2.55/1.39  Main loop            : 0.23
% 2.55/1.39  Inferencing          : 0.08
% 2.55/1.39  Reduction            : 0.07
% 2.55/1.39  Demodulation         : 0.04
% 2.55/1.39  BG Simplification    : 0.02
% 2.55/1.39  Subsumption          : 0.04
% 2.55/1.39  Abstraction          : 0.02
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.60
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
