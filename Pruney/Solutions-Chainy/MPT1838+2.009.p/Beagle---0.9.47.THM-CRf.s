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
% DateTime   : Thu Dec  3 10:28:15 EST 2020

% Result     : Theorem 18.24s
% Output     : CNFRefutation 18.24s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 196 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_66,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    ! [A_41] :
      ( k6_domain_1(A_41,'#skF_5'(A_41)) = A_41
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_60,plain,(
    ! [A_41] :
      ( m1_subset_1('#skF_5'(A_41),A_41)
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1032,plain,(
    ! [A_135,B_136] :
      ( k6_domain_1(A_135,B_136) = k1_tarski(B_136)
      | ~ m1_subset_1(B_136,A_135)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5324,plain,(
    ! [A_292] :
      ( k6_domain_1(A_292,'#skF_5'(A_292)) = k1_tarski('#skF_5'(A_292))
      | ~ v1_zfmisc_1(A_292)
      | v1_xboole_0(A_292) ) ),
    inference(resolution,[status(thm)],[c_60,c_1032])).

tff(c_54392,plain,(
    ! [A_845] :
      ( k1_tarski('#skF_5'(A_845)) = A_845
      | ~ v1_zfmisc_1(A_845)
      | v1_xboole_0(A_845)
      | ~ v1_zfmisc_1(A_845)
      | v1_xboole_0(A_845) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_5324])).

tff(c_62,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_196,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tarski(A_63),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_609,plain,(
    ! [A_120,B_121] :
      ( k2_xboole_0(k1_tarski(A_120),B_121) = B_121
      | ~ r2_hidden(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_196,c_34])).

tff(c_52,plain,(
    ! [A_37,B_38] : k2_xboole_0(k1_tarski(A_37),B_38) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_708,plain,(
    ! [B_122,A_123] :
      ( k1_xboole_0 != B_122
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_52])).

tff(c_743,plain,(
    ! [A_124] :
      ( k1_xboole_0 != A_124
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_6,c_708])).

tff(c_774,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_743,c_70])).

tff(c_64,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_145,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(A_59,B_60) = B_60
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_157,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_349,plain,(
    ! [D_96,A_97,B_98] :
      ( ~ r2_hidden(D_96,A_97)
      | r2_hidden(D_96,k2_xboole_0(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_362,plain,(
    ! [D_96] :
      ( ~ r2_hidden(D_96,'#skF_6')
      | r2_hidden(D_96,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_349])).

tff(c_733,plain,(
    ! [D_96] :
      ( k1_xboole_0 != '#skF_7'
      | ~ r2_hidden(D_96,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_362,c_708])).

tff(c_741,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_1873,plain,(
    ! [C_180,B_181,A_182] :
      ( k1_xboole_0 = C_180
      | k1_xboole_0 = B_181
      | C_180 = B_181
      | k2_xboole_0(B_181,C_180) != k1_tarski(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1894,plain,(
    ! [A_182] :
      ( k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | '#skF_7' = '#skF_6'
      | k1_tarski(A_182) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_1873])).

tff(c_1903,plain,(
    ! [A_182] : k1_tarski(A_182) != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_774,c_741,c_1894])).

tff(c_54544,plain,(
    ! [A_846] :
      ( A_846 != '#skF_7'
      | ~ v1_zfmisc_1(A_846)
      | v1_xboole_0(A_846)
      | ~ v1_zfmisc_1(A_846)
      | v1_xboole_0(A_846) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54392,c_1903])).

tff(c_54546,plain,
    ( ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_54544])).

tff(c_54549,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54546])).

tff(c_54551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_54549])).

tff(c_54562,plain,(
    ! [D_847] : ~ r2_hidden(D_847,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_54570,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_54562])).

tff(c_54575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_54570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:38:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.24/9.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.24/9.34  
% 18.24/9.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.24/9.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2
% 18.24/9.34  
% 18.24/9.34  %Foreground sorts:
% 18.24/9.34  
% 18.24/9.34  
% 18.24/9.34  %Background operators:
% 18.24/9.34  
% 18.24/9.34  
% 18.24/9.34  %Foreground operators:
% 18.24/9.34  tff('#skF_5', type, '#skF_5': $i > $i).
% 18.24/9.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.24/9.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.24/9.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.24/9.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.24/9.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 18.24/9.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.24/9.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 18.24/9.34  tff('#skF_7', type, '#skF_7': $i).
% 18.24/9.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 18.24/9.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.24/9.34  tff('#skF_6', type, '#skF_6': $i).
% 18.24/9.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.24/9.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.24/9.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.24/9.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.24/9.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.24/9.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 18.24/9.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.24/9.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.24/9.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.24/9.34  
% 18.24/9.35  tff(f_125, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 18.24/9.35  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 18.24/9.35  tff(f_111, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 18.24/9.35  tff(f_101, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 18.24/9.35  tff(f_79, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 18.24/9.35  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.24/9.35  tff(f_94, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 18.24/9.35  tff(f_49, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 18.24/9.35  tff(f_91, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 18.24/9.35  tff(c_70, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.24/9.35  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.24/9.35  tff(c_68, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.24/9.35  tff(c_66, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.24/9.35  tff(c_58, plain, (![A_41]: (k6_domain_1(A_41, '#skF_5'(A_41))=A_41 | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.24/9.35  tff(c_60, plain, (![A_41]: (m1_subset_1('#skF_5'(A_41), A_41) | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.24/9.35  tff(c_1032, plain, (![A_135, B_136]: (k6_domain_1(A_135, B_136)=k1_tarski(B_136) | ~m1_subset_1(B_136, A_135) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.24/9.35  tff(c_5324, plain, (![A_292]: (k6_domain_1(A_292, '#skF_5'(A_292))=k1_tarski('#skF_5'(A_292)) | ~v1_zfmisc_1(A_292) | v1_xboole_0(A_292))), inference(resolution, [status(thm)], [c_60, c_1032])).
% 18.24/9.35  tff(c_54392, plain, (![A_845]: (k1_tarski('#skF_5'(A_845))=A_845 | ~v1_zfmisc_1(A_845) | v1_xboole_0(A_845) | ~v1_zfmisc_1(A_845) | v1_xboole_0(A_845))), inference(superposition, [status(thm), theory('equality')], [c_58, c_5324])).
% 18.24/9.35  tff(c_62, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.24/9.35  tff(c_196, plain, (![A_63, B_64]: (r1_tarski(k1_tarski(A_63), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 18.24/9.35  tff(c_34, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.24/9.35  tff(c_609, plain, (![A_120, B_121]: (k2_xboole_0(k1_tarski(A_120), B_121)=B_121 | ~r2_hidden(A_120, B_121))), inference(resolution, [status(thm)], [c_196, c_34])).
% 18.24/9.35  tff(c_52, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_94])).
% 18.24/9.35  tff(c_708, plain, (![B_122, A_123]: (k1_xboole_0!=B_122 | ~r2_hidden(A_123, B_122))), inference(superposition, [status(thm), theory('equality')], [c_609, c_52])).
% 18.24/9.35  tff(c_743, plain, (![A_124]: (k1_xboole_0!=A_124 | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_6, c_708])).
% 18.24/9.35  tff(c_774, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_743, c_70])).
% 18.24/9.35  tff(c_64, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.24/9.35  tff(c_145, plain, (![A_59, B_60]: (k2_xboole_0(A_59, B_60)=B_60 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.24/9.35  tff(c_157, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_64, c_145])).
% 18.24/9.35  tff(c_349, plain, (![D_96, A_97, B_98]: (~r2_hidden(D_96, A_97) | r2_hidden(D_96, k2_xboole_0(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.24/9.35  tff(c_362, plain, (![D_96]: (~r2_hidden(D_96, '#skF_6') | r2_hidden(D_96, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_349])).
% 18.24/9.35  tff(c_733, plain, (![D_96]: (k1_xboole_0!='#skF_7' | ~r2_hidden(D_96, '#skF_6'))), inference(resolution, [status(thm)], [c_362, c_708])).
% 18.24/9.35  tff(c_741, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_733])).
% 18.24/9.35  tff(c_1873, plain, (![C_180, B_181, A_182]: (k1_xboole_0=C_180 | k1_xboole_0=B_181 | C_180=B_181 | k2_xboole_0(B_181, C_180)!=k1_tarski(A_182))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.24/9.35  tff(c_1894, plain, (![A_182]: (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | '#skF_7'='#skF_6' | k1_tarski(A_182)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_157, c_1873])).
% 18.24/9.35  tff(c_1903, plain, (![A_182]: (k1_tarski(A_182)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_774, c_741, c_1894])).
% 18.24/9.35  tff(c_54544, plain, (![A_846]: (A_846!='#skF_7' | ~v1_zfmisc_1(A_846) | v1_xboole_0(A_846) | ~v1_zfmisc_1(A_846) | v1_xboole_0(A_846))), inference(superposition, [status(thm), theory('equality')], [c_54392, c_1903])).
% 18.24/9.35  tff(c_54546, plain, (~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_54544])).
% 18.24/9.35  tff(c_54549, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54546])).
% 18.24/9.35  tff(c_54551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_54549])).
% 18.24/9.35  tff(c_54562, plain, (![D_847]: (~r2_hidden(D_847, '#skF_6'))), inference(splitRight, [status(thm)], [c_733])).
% 18.24/9.35  tff(c_54570, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_54562])).
% 18.24/9.35  tff(c_54575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_54570])).
% 18.24/9.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.24/9.35  
% 18.24/9.35  Inference rules
% 18.24/9.35  ----------------------
% 18.24/9.35  #Ref     : 11
% 18.24/9.35  #Sup     : 14589
% 18.24/9.35  #Fact    : 42
% 18.24/9.35  #Define  : 0
% 18.24/9.35  #Split   : 11
% 18.24/9.35  #Chain   : 0
% 18.24/9.35  #Close   : 0
% 18.24/9.35  
% 18.24/9.35  Ordering : KBO
% 18.24/9.35  
% 18.24/9.35  Simplification rules
% 18.24/9.35  ----------------------
% 18.24/9.35  #Subsume      : 6566
% 18.24/9.35  #Demod        : 9406
% 18.24/9.35  #Tautology    : 3406
% 18.24/9.35  #SimpNegUnit  : 460
% 18.24/9.35  #BackRed      : 64
% 18.24/9.35  
% 18.24/9.35  #Partial instantiations: 0
% 18.24/9.35  #Strategies tried      : 1
% 18.24/9.35  
% 18.24/9.35  Timing (in seconds)
% 18.24/9.35  ----------------------
% 18.24/9.35  Preprocessing        : 0.34
% 18.24/9.35  Parsing              : 0.17
% 18.24/9.35  CNF conversion       : 0.03
% 18.24/9.35  Main loop            : 8.26
% 18.24/9.35  Inferencing          : 1.23
% 18.24/9.35  Reduction            : 3.93
% 18.24/9.36  Demodulation         : 3.26
% 18.24/9.36  BG Simplification    : 0.15
% 18.24/9.36  Subsumption          : 2.55
% 18.24/9.36  Abstraction          : 0.22
% 18.24/9.36  MUC search           : 0.00
% 18.24/9.36  Cooper               : 0.00
% 18.24/9.36  Total                : 8.63
% 18.24/9.36  Index Insertion      : 0.00
% 18.24/9.36  Index Deletion       : 0.00
% 18.24/9.36  Index Matching       : 0.00
% 18.24/9.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
