%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:58 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 109 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 261 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_102,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111,plain,(
    v4_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_5'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_244,plain,(
    ! [A_122,C_123] :
      ( r2_hidden('#skF_5'(A_122,k2_relat_1(A_122),C_123),k1_relat_1(A_122))
      | ~ r2_hidden(C_123,k2_relat_1(A_122))
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_472,plain,(
    ! [A_192,C_193,B_194] :
      ( r2_hidden('#skF_5'(A_192,k2_relat_1(A_192),C_193),B_194)
      | ~ r1_tarski(k1_relat_1(A_192),B_194)
      | ~ r2_hidden(C_193,k2_relat_1(A_192))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_480,plain,(
    ! [A_195,C_196,B_197] :
      ( m1_subset_1('#skF_5'(A_195,k2_relat_1(A_195),C_196),B_197)
      | ~ r1_tarski(k1_relat_1(A_195),B_197)
      | ~ r2_hidden(C_196,k2_relat_1(A_195))
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(resolution,[status(thm)],[c_472,c_8])).

tff(c_40,plain,(
    ! [E_60] :
      ( k1_funct_1('#skF_9',E_60) != '#skF_6'
      | ~ m1_subset_1(E_60,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_506,plain,(
    ! [A_198,C_199] :
      ( k1_funct_1('#skF_9','#skF_5'(A_198,k2_relat_1(A_198),C_199)) != '#skF_6'
      | ~ r1_tarski(k1_relat_1(A_198),'#skF_7')
      | ~ r2_hidden(C_199,k2_relat_1(A_198))
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_480,c_40])).

tff(c_510,plain,(
    ! [C_46] :
      ( C_46 != '#skF_6'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_506])).

tff(c_512,plain,(
    ! [C_46] :
      ( C_46 != '#skF_6'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_48,c_70,c_48,c_510])).

tff(c_513,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_516,plain,
    ( ~ v4_relat_1('#skF_9','#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_12,c_513])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_111,c_516])).

tff(c_535,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_164,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_178,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_42,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_181,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_42])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.48  
% 2.91/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.91/1.48  
% 2.91/1.48  %Foreground sorts:
% 2.91/1.48  
% 2.91/1.48  
% 2.91/1.48  %Background operators:
% 2.91/1.48  
% 2.91/1.48  
% 2.91/1.48  %Foreground operators:
% 2.91/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.91/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.91/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.91/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.91/1.48  tff('#skF_9', type, '#skF_9': $i).
% 2.91/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.91/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.91/1.48  tff('#skF_8', type, '#skF_8': $i).
% 2.91/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.91/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.91/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.48  
% 2.91/1.49  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.91/1.49  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.91/1.49  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.91/1.49  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.91/1.49  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.91/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.91/1.49  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.91/1.49  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.91/1.49  tff(c_44, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.49  tff(c_66, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.91/1.49  tff(c_70, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_66])).
% 2.91/1.49  tff(c_102, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.91/1.49  tff(c_111, plain, (v4_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_102])).
% 2.91/1.49  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.49  tff(c_48, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.49  tff(c_16, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_5'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.91/1.49  tff(c_244, plain, (![A_122, C_123]: (r2_hidden('#skF_5'(A_122, k2_relat_1(A_122), C_123), k1_relat_1(A_122)) | ~r2_hidden(C_123, k2_relat_1(A_122)) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.91/1.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.49  tff(c_472, plain, (![A_192, C_193, B_194]: (r2_hidden('#skF_5'(A_192, k2_relat_1(A_192), C_193), B_194) | ~r1_tarski(k1_relat_1(A_192), B_194) | ~r2_hidden(C_193, k2_relat_1(A_192)) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_244, c_2])).
% 2.91/1.49  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.49  tff(c_480, plain, (![A_195, C_196, B_197]: (m1_subset_1('#skF_5'(A_195, k2_relat_1(A_195), C_196), B_197) | ~r1_tarski(k1_relat_1(A_195), B_197) | ~r2_hidden(C_196, k2_relat_1(A_195)) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(resolution, [status(thm)], [c_472, c_8])).
% 2.91/1.49  tff(c_40, plain, (![E_60]: (k1_funct_1('#skF_9', E_60)!='#skF_6' | ~m1_subset_1(E_60, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.49  tff(c_506, plain, (![A_198, C_199]: (k1_funct_1('#skF_9', '#skF_5'(A_198, k2_relat_1(A_198), C_199))!='#skF_6' | ~r1_tarski(k1_relat_1(A_198), '#skF_7') | ~r2_hidden(C_199, k2_relat_1(A_198)) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_480, c_40])).
% 2.91/1.49  tff(c_510, plain, (![C_46]: (C_46!='#skF_6' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_46, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_46, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_506])).
% 2.91/1.49  tff(c_512, plain, (![C_46]: (C_46!='#skF_6' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_46, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_48, c_70, c_48, c_510])).
% 2.91/1.49  tff(c_513, plain, (~r1_tarski(k1_relat_1('#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_512])).
% 2.91/1.49  tff(c_516, plain, (~v4_relat_1('#skF_9', '#skF_7') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_12, c_513])).
% 2.91/1.49  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_111, c_516])).
% 2.91/1.49  tff(c_535, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_512])).
% 2.91/1.49  tff(c_164, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.91/1.49  tff(c_178, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_164])).
% 2.91/1.49  tff(c_42, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.49  tff(c_181, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_42])).
% 2.91/1.49  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_535, c_181])).
% 2.91/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.49  
% 2.91/1.49  Inference rules
% 2.91/1.49  ----------------------
% 2.91/1.49  #Ref     : 0
% 2.91/1.49  #Sup     : 104
% 2.91/1.49  #Fact    : 0
% 2.91/1.49  #Define  : 0
% 2.91/1.49  #Split   : 1
% 2.91/1.49  #Chain   : 0
% 2.91/1.49  #Close   : 0
% 2.91/1.49  
% 2.91/1.49  Ordering : KBO
% 2.91/1.49  
% 2.91/1.49  Simplification rules
% 2.91/1.49  ----------------------
% 2.91/1.49  #Subsume      : 14
% 2.91/1.49  #Demod        : 14
% 2.91/1.49  #Tautology    : 13
% 2.91/1.49  #SimpNegUnit  : 1
% 2.91/1.49  #BackRed      : 4
% 2.91/1.49  
% 2.91/1.49  #Partial instantiations: 0
% 2.91/1.49  #Strategies tried      : 1
% 2.91/1.49  
% 2.91/1.49  Timing (in seconds)
% 2.91/1.49  ----------------------
% 2.91/1.50  Preprocessing        : 0.32
% 2.91/1.50  Parsing              : 0.17
% 2.91/1.50  CNF conversion       : 0.03
% 2.91/1.50  Main loop            : 0.41
% 2.91/1.50  Inferencing          : 0.15
% 2.91/1.50  Reduction            : 0.10
% 2.91/1.50  Demodulation         : 0.08
% 2.91/1.50  BG Simplification    : 0.02
% 2.91/1.50  Subsumption          : 0.09
% 2.91/1.50  Abstraction          : 0.02
% 2.91/1.50  MUC search           : 0.00
% 2.91/1.50  Cooper               : 0.00
% 2.91/1.50  Total                : 0.76
% 2.91/1.50  Index Insertion      : 0.00
% 2.91/1.50  Index Deletion       : 0.00
% 2.91/1.50  Index Matching       : 0.00
% 2.91/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
