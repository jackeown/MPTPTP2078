%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:38 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 121 expanded)
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_90,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_123,plain,(
    ! [A_50,B_51] :
      ( k6_domain_1(A_50,B_51) = k1_tarski(B_51)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_126,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_129,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_126])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_130,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_42])).

tff(c_141,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k6_domain_1(A_54,B_55),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_141])).

tff(c_154,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_150])).

tff(c_155,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_154])).

tff(c_166,plain,(
    ! [B_56,A_57] :
      ( ~ v1_subset_1(B_56,A_57)
      | v1_xboole_0(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_169,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_166])).

tff(c_175,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_130,c_169])).

tff(c_176,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_175])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_89,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_183,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_176,c_92])).

tff(c_49,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [D_9,B_5] : r2_hidden(D_9,k2_tarski(D_9,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_12])).

tff(c_67,plain,(
    ! [B_33,A_34] :
      ( ~ r1_tarski(B_33,A_34)
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    ! [A_29] : ~ r1_tarski(k1_tarski(A_29),A_29) ),
    inference(resolution,[status(thm)],[c_55,c_67])).

tff(c_196,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_78])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.15/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.15/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.15/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.26  
% 2.15/1.27  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.27  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.15/1.27  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.15/1.27  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.15/1.27  tff(f_90, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.15/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.27  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.15/1.27  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.27  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.15/1.27  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.15/1.27  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.15/1.27  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.15/1.27  tff(c_40, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.15/1.27  tff(c_44, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.15/1.27  tff(c_123, plain, (![A_50, B_51]: (k6_domain_1(A_50, B_51)=k1_tarski(B_51) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.27  tff(c_126, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_123])).
% 2.15/1.27  tff(c_129, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_126])).
% 2.15/1.27  tff(c_42, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.15/1.27  tff(c_130, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_42])).
% 2.15/1.27  tff(c_141, plain, (![A_54, B_55]: (m1_subset_1(k6_domain_1(A_54, B_55), k1_zfmisc_1(A_54)) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.15/1.27  tff(c_150, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_129, c_141])).
% 2.15/1.27  tff(c_154, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_150])).
% 2.15/1.27  tff(c_155, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_154])).
% 2.15/1.27  tff(c_166, plain, (![B_56, A_57]: (~v1_subset_1(B_56, A_57) | v1_xboole_0(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.15/1.27  tff(c_169, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_155, c_166])).
% 2.15/1.27  tff(c_175, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_130, c_169])).
% 2.15/1.27  tff(c_176, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_175])).
% 2.15/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.27  tff(c_89, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.15/1.27  tff(c_92, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_2, c_89])).
% 2.15/1.27  tff(c_183, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_176, c_92])).
% 2.15/1.27  tff(c_49, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.27  tff(c_12, plain, (![D_9, B_5]: (r2_hidden(D_9, k2_tarski(D_9, B_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.27  tff(c_55, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_12])).
% 2.15/1.27  tff(c_67, plain, (![B_33, A_34]: (~r1_tarski(B_33, A_34) | ~r2_hidden(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.27  tff(c_78, plain, (![A_29]: (~r1_tarski(k1_tarski(A_29), A_29))), inference(resolution, [status(thm)], [c_55, c_67])).
% 2.15/1.27  tff(c_196, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_183, c_78])).
% 2.15/1.27  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_196])).
% 2.15/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  Inference rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Ref     : 0
% 2.15/1.27  #Sup     : 34
% 2.15/1.27  #Fact    : 0
% 2.15/1.27  #Define  : 0
% 2.15/1.27  #Split   : 0
% 2.15/1.27  #Chain   : 0
% 2.15/1.27  #Close   : 0
% 2.15/1.27  
% 2.15/1.27  Ordering : KBO
% 2.15/1.27  
% 2.15/1.27  Simplification rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Subsume      : 3
% 2.15/1.27  #Demod        : 12
% 2.15/1.27  #Tautology    : 14
% 2.15/1.27  #SimpNegUnit  : 3
% 2.15/1.27  #BackRed      : 5
% 2.15/1.27  
% 2.15/1.27  #Partial instantiations: 0
% 2.15/1.27  #Strategies tried      : 1
% 2.15/1.27  
% 2.15/1.27  Timing (in seconds)
% 2.15/1.27  ----------------------
% 2.15/1.27  Preprocessing        : 0.32
% 2.15/1.27  Parsing              : 0.17
% 2.15/1.27  CNF conversion       : 0.02
% 2.15/1.27  Main loop            : 0.15
% 2.15/1.27  Inferencing          : 0.05
% 2.15/1.28  Reduction            : 0.05
% 2.15/1.28  Demodulation         : 0.03
% 2.15/1.28  BG Simplification    : 0.02
% 2.15/1.28  Subsumption          : 0.03
% 2.15/1.28  Abstraction          : 0.01
% 2.15/1.28  MUC search           : 0.00
% 2.15/1.28  Cooper               : 0.00
% 2.15/1.28  Total                : 0.50
% 2.15/1.28  Index Insertion      : 0.00
% 2.15/1.28  Index Deletion       : 0.00
% 2.15/1.28  Index Matching       : 0.00
% 2.15/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
