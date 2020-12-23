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
% DateTime   : Thu Dec  3 10:28:36 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 123 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [A_35,B_36] : k2_xboole_0(k1_tarski(A_35),B_36) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_35] : k1_tarski(A_35) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_57])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_172,plain,(
    ! [A_67,B_68] :
      ( k6_domain_1(A_67,B_68) = k1_tarski(B_68)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_175,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_178,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_175])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_179,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_40])).

tff(c_197,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_206,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_197])).

tff(c_210,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_206])).

tff(c_211,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_210])).

tff(c_473,plain,(
    ! [B_109,A_110] :
      ( ~ v1_subset_1(B_109,A_110)
      | v1_xboole_0(B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_110))
      | ~ v1_zfmisc_1(A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_479,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_473])).

tff(c_488,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_179,c_479])).

tff(c_489,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_488])).

tff(c_111,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_51,B_52] :
      ( ~ v1_xboole_0(A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_129,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_122,c_96])).

tff(c_495,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_489,c_129])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:38:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.65/1.39  
% 2.65/1.39  %Foreground sorts:
% 2.65/1.39  
% 2.65/1.39  
% 2.65/1.39  %Background operators:
% 2.65/1.39  
% 2.65/1.39  
% 2.65/1.39  %Foreground operators:
% 2.65/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.65/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.65/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.65/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.65/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.39  
% 2.65/1.40  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.65/1.40  tff(f_57, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.65/1.40  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.65/1.40  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.65/1.40  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.65/1.40  tff(f_93, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.65/1.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.65/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.65/1.40  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.40  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.40  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.40  tff(c_57, plain, (![A_35, B_36]: (k2_xboole_0(k1_tarski(A_35), B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.40  tff(c_61, plain, (![A_35]: (k1_tarski(A_35)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_57])).
% 2.65/1.40  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.65/1.40  tff(c_38, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.65/1.40  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.65/1.40  tff(c_172, plain, (![A_67, B_68]: (k6_domain_1(A_67, B_68)=k1_tarski(B_68) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.40  tff(c_175, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_172])).
% 2.65/1.40  tff(c_178, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_175])).
% 2.65/1.40  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.65/1.40  tff(c_179, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_40])).
% 2.65/1.40  tff(c_197, plain, (![A_71, B_72]: (m1_subset_1(k6_domain_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.40  tff(c_206, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_197])).
% 2.65/1.40  tff(c_210, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_206])).
% 2.65/1.40  tff(c_211, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_210])).
% 2.65/1.40  tff(c_473, plain, (![B_109, A_110]: (~v1_subset_1(B_109, A_110) | v1_xboole_0(B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_110)) | ~v1_zfmisc_1(A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.65/1.40  tff(c_479, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_211, c_473])).
% 2.65/1.40  tff(c_488, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_179, c_479])).
% 2.65/1.40  tff(c_489, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_488])).
% 2.65/1.40  tff(c_111, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.65/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.40  tff(c_122, plain, (![A_51, B_52]: (~v1_xboole_0(A_51) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_111, c_2])).
% 2.65/1.40  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.65/1.40  tff(c_87, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.65/1.40  tff(c_96, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_87])).
% 2.65/1.40  tff(c_129, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_122, c_96])).
% 2.65/1.40  tff(c_495, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_489, c_129])).
% 2.65/1.40  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_495])).
% 2.65/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  Inference rules
% 2.65/1.40  ----------------------
% 2.65/1.40  #Ref     : 0
% 2.65/1.40  #Sup     : 99
% 2.65/1.40  #Fact    : 0
% 2.65/1.40  #Define  : 0
% 2.65/1.40  #Split   : 2
% 2.65/1.40  #Chain   : 0
% 2.65/1.40  #Close   : 0
% 2.65/1.40  
% 2.65/1.40  Ordering : KBO
% 2.65/1.40  
% 2.65/1.40  Simplification rules
% 2.65/1.40  ----------------------
% 2.65/1.40  #Subsume      : 24
% 2.65/1.40  #Demod        : 28
% 2.65/1.40  #Tautology    : 39
% 2.65/1.40  #SimpNegUnit  : 15
% 2.65/1.40  #BackRed      : 7
% 2.65/1.40  
% 2.65/1.40  #Partial instantiations: 0
% 2.65/1.40  #Strategies tried      : 1
% 2.65/1.40  
% 2.65/1.40  Timing (in seconds)
% 2.65/1.40  ----------------------
% 2.65/1.41  Preprocessing        : 0.33
% 2.65/1.41  Parsing              : 0.18
% 2.65/1.41  CNF conversion       : 0.02
% 2.65/1.41  Main loop            : 0.27
% 2.65/1.41  Inferencing          : 0.10
% 2.65/1.41  Reduction            : 0.08
% 2.65/1.41  Demodulation         : 0.05
% 2.65/1.41  BG Simplification    : 0.02
% 2.65/1.41  Subsumption          : 0.06
% 2.65/1.41  Abstraction          : 0.02
% 2.65/1.41  MUC search           : 0.00
% 2.65/1.41  Cooper               : 0.00
% 2.65/1.41  Total                : 0.64
% 2.65/1.41  Index Insertion      : 0.00
% 2.65/1.41  Index Deletion       : 0.00
% 2.65/1.41  Index Matching       : 0.00
% 2.65/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
