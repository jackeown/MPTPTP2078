%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 124 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 291 expanded)
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

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_66])).

tff(c_100,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    v4_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_15,C_51] :
      ( k1_funct_1(A_15,'#skF_5'(A_15,k2_relat_1(A_15),C_51)) = C_51
      | ~ r2_hidden(C_51,k2_relat_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_268,plain,(
    ! [A_134,C_135] :
      ( r2_hidden('#skF_5'(A_134,k2_relat_1(A_134),C_135),k1_relat_1(A_134))
      | ~ r2_hidden(C_135,k2_relat_1(A_134))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_472,plain,(
    ! [A_189,C_190,B_191] :
      ( r2_hidden('#skF_5'(A_189,k2_relat_1(A_189),C_190),B_191)
      | ~ r1_tarski(k1_relat_1(A_189),B_191)
      | ~ r2_hidden(C_190,k2_relat_1(A_189))
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_268,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_480,plain,(
    ! [A_192,C_193,B_194] :
      ( m1_subset_1('#skF_5'(A_192,k2_relat_1(A_192),C_193),B_194)
      | ~ r1_tarski(k1_relat_1(A_192),B_194)
      | ~ r2_hidden(C_193,k2_relat_1(A_192))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_472,c_8])).

tff(c_42,plain,(
    ! [E_62] :
      ( k1_funct_1('#skF_9',E_62) != '#skF_6'
      | ~ m1_subset_1(E_62,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_506,plain,(
    ! [A_195,C_196] :
      ( k1_funct_1('#skF_9','#skF_5'(A_195,k2_relat_1(A_195),C_196)) != '#skF_6'
      | ~ r1_tarski(k1_relat_1(A_195),'#skF_7')
      | ~ r2_hidden(C_196,k2_relat_1(A_195))
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(resolution,[status(thm)],[c_480,c_42])).

tff(c_510,plain,(
    ! [C_51] :
      ( C_51 != '#skF_6'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_506])).

tff(c_512,plain,(
    ! [C_51] :
      ( C_51 != '#skF_6'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_50,c_69,c_50,c_510])).

tff(c_513,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_516,plain,
    ( ~ v4_relat_1('#skF_9','#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_14,c_513])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_109,c_516])).

tff(c_535,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_148,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_157,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_148])).

tff(c_44,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_160,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_44])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.60  
% 2.84/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.84/1.61  
% 2.84/1.61  %Foreground sorts:
% 2.84/1.61  
% 2.84/1.61  
% 2.84/1.61  %Background operators:
% 2.84/1.61  
% 2.84/1.61  
% 2.84/1.61  %Foreground operators:
% 2.84/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.84/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.61  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.84/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.84/1.61  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.84/1.61  tff('#skF_9', type, '#skF_9': $i).
% 2.84/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.84/1.61  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.84/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.61  
% 2.84/1.62  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.84/1.62  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.84/1.62  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.84/1.62  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.62  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.84/1.62  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.84/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.84/1.62  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.84/1.62  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.84/1.62  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.62  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.62  tff(c_63, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.62  tff(c_66, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_46, c_63])).
% 2.84/1.62  tff(c_69, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_66])).
% 2.84/1.62  tff(c_100, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.62  tff(c_109, plain, (v4_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_100])).
% 2.84/1.62  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.62  tff(c_50, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.62  tff(c_20, plain, (![A_15, C_51]: (k1_funct_1(A_15, '#skF_5'(A_15, k2_relat_1(A_15), C_51))=C_51 | ~r2_hidden(C_51, k2_relat_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.62  tff(c_268, plain, (![A_134, C_135]: (r2_hidden('#skF_5'(A_134, k2_relat_1(A_134), C_135), k1_relat_1(A_134)) | ~r2_hidden(C_135, k2_relat_1(A_134)) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.62  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.62  tff(c_472, plain, (![A_189, C_190, B_191]: (r2_hidden('#skF_5'(A_189, k2_relat_1(A_189), C_190), B_191) | ~r1_tarski(k1_relat_1(A_189), B_191) | ~r2_hidden(C_190, k2_relat_1(A_189)) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_268, c_2])).
% 2.84/1.62  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.84/1.62  tff(c_480, plain, (![A_192, C_193, B_194]: (m1_subset_1('#skF_5'(A_192, k2_relat_1(A_192), C_193), B_194) | ~r1_tarski(k1_relat_1(A_192), B_194) | ~r2_hidden(C_193, k2_relat_1(A_192)) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_472, c_8])).
% 2.84/1.62  tff(c_42, plain, (![E_62]: (k1_funct_1('#skF_9', E_62)!='#skF_6' | ~m1_subset_1(E_62, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.62  tff(c_506, plain, (![A_195, C_196]: (k1_funct_1('#skF_9', '#skF_5'(A_195, k2_relat_1(A_195), C_196))!='#skF_6' | ~r1_tarski(k1_relat_1(A_195), '#skF_7') | ~r2_hidden(C_196, k2_relat_1(A_195)) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(resolution, [status(thm)], [c_480, c_42])).
% 2.84/1.62  tff(c_510, plain, (![C_51]: (C_51!='#skF_6' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_51, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_51, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_506])).
% 2.84/1.62  tff(c_512, plain, (![C_51]: (C_51!='#skF_6' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_51, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_50, c_69, c_50, c_510])).
% 2.84/1.62  tff(c_513, plain, (~r1_tarski(k1_relat_1('#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_512])).
% 2.84/1.62  tff(c_516, plain, (~v4_relat_1('#skF_9', '#skF_7') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_14, c_513])).
% 2.84/1.62  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_109, c_516])).
% 2.84/1.62  tff(c_535, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_512])).
% 2.84/1.62  tff(c_148, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.62  tff(c_157, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_148])).
% 2.84/1.62  tff(c_44, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.62  tff(c_160, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_44])).
% 2.84/1.62  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_535, c_160])).
% 2.84/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.62  
% 2.84/1.62  Inference rules
% 2.84/1.62  ----------------------
% 2.84/1.62  #Ref     : 0
% 2.84/1.62  #Sup     : 102
% 2.84/1.62  #Fact    : 0
% 2.84/1.62  #Define  : 0
% 2.84/1.62  #Split   : 1
% 2.84/1.62  #Chain   : 0
% 2.84/1.62  #Close   : 0
% 2.84/1.62  
% 2.84/1.62  Ordering : KBO
% 2.84/1.62  
% 2.84/1.62  Simplification rules
% 2.84/1.62  ----------------------
% 2.84/1.62  #Subsume      : 14
% 2.84/1.62  #Demod        : 15
% 2.84/1.62  #Tautology    : 13
% 2.84/1.62  #SimpNegUnit  : 1
% 2.84/1.62  #BackRed      : 4
% 2.84/1.62  
% 2.84/1.62  #Partial instantiations: 0
% 2.84/1.62  #Strategies tried      : 1
% 2.84/1.62  
% 2.84/1.62  Timing (in seconds)
% 2.84/1.62  ----------------------
% 2.84/1.62  Preprocessing        : 0.45
% 2.84/1.62  Parsing              : 0.27
% 2.84/1.62  CNF conversion       : 0.03
% 2.84/1.62  Main loop            : 0.33
% 2.84/1.62  Inferencing          : 0.13
% 2.84/1.62  Reduction            : 0.08
% 2.84/1.62  Demodulation         : 0.06
% 2.84/1.62  BG Simplification    : 0.02
% 2.84/1.62  Subsumption          : 0.07
% 2.84/1.62  Abstraction          : 0.02
% 2.84/1.62  MUC search           : 0.00
% 2.84/1.62  Cooper               : 0.00
% 2.84/1.62  Total                : 0.81
% 2.84/1.62  Index Insertion      : 0.00
% 2.84/1.62  Index Deletion       : 0.00
% 2.84/1.62  Index Matching       : 0.00
% 2.84/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
