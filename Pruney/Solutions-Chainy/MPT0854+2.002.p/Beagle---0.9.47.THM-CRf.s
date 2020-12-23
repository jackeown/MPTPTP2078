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
% DateTime   : Thu Dec  3 10:08:51 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 175 expanded)
%              Number of leaves         :   31 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 292 expanded)
%              Number of equality atoms :   25 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_48,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_6'),'#skF_8')
    | ~ r2_hidden(k1_mcart_1('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_90,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    r2_hidden('#skF_6',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    ! [A_64,A_65,B_66] :
      ( v1_relat_1(A_64)
      | ~ r1_tarski(A_64,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_115,plain,(
    ! [A_67,A_68,B_69] :
      ( v1_relat_1(k1_tarski(A_67))
      | ~ r2_hidden(A_67,k2_zfmisc_1(A_68,B_69)) ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_124,plain,(
    v1_relat_1(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [D_42,B_43] : r2_hidden(D_42,k2_tarski(D_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_69])).

tff(c_159,plain,(
    ! [A_86,B_87] :
      ( k4_tarski('#skF_4'(A_86,B_87),'#skF_5'(A_86,B_87)) = B_87
      | ~ r2_hidden(B_87,A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_37,B_38] : k2_mcart_1(k4_tarski(A_37,B_38)) = B_38 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_280,plain,(
    ! [B_105,A_106] :
      ( k2_mcart_1(B_105) = '#skF_5'(A_106,B_105)
      | ~ r2_hidden(B_105,A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_46])).

tff(c_319,plain,(
    ! [A_110] :
      ( '#skF_5'(k1_tarski(A_110),A_110) = k2_mcart_1(A_110)
      | ~ v1_relat_1(k1_tarski(A_110)) ) ),
    inference(resolution,[status(thm)],[c_72,c_280])).

tff(c_325,plain,(
    '#skF_5'(k1_tarski('#skF_6'),'#skF_6') = k2_mcart_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_319])).

tff(c_36,plain,(
    ! [A_16,B_31] :
      ( k4_tarski('#skF_4'(A_16,B_31),'#skF_5'(A_16,B_31)) = B_31
      | ~ r2_hidden(B_31,A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_329,plain,
    ( k4_tarski('#skF_4'(k1_tarski('#skF_6'),'#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ v1_relat_1(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_36])).

tff(c_333,plain,(
    k4_tarski('#skF_4'(k1_tarski('#skF_6'),'#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72,c_329])).

tff(c_44,plain,(
    ! [A_37,B_38] : k1_mcart_1(k4_tarski(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_351,plain,(
    '#skF_4'(k1_tarski('#skF_6'),'#skF_6') = k1_mcart_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_44])).

tff(c_373,plain,(
    k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_333])).

tff(c_30,plain,(
    ! [A_10,C_12,B_11,D_13] :
      ( r2_hidden(A_10,C_12)
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_470,plain,(
    ! [C_122,D_123] :
      ( r2_hidden(k1_mcart_1('#skF_6'),C_122)
      | ~ r2_hidden('#skF_6',k2_zfmisc_1(C_122,D_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_30])).

tff(c_472,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_470])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_472])).

tff(c_477,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_491,plain,(
    ! [C_132,A_133,B_134] :
      ( v1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_497,plain,(
    ! [A_135,A_136,B_137] :
      ( v1_relat_1(A_135)
      | ~ r1_tarski(A_135,k2_zfmisc_1(A_136,B_137)) ) ),
    inference(resolution,[status(thm)],[c_34,c_491])).

tff(c_503,plain,(
    ! [A_138,A_139,B_140] :
      ( v1_relat_1(k1_tarski(A_138))
      | ~ r2_hidden(A_138,k2_zfmisc_1(A_139,B_140)) ) ),
    inference(resolution,[status(thm)],[c_24,c_497])).

tff(c_512,plain,(
    v1_relat_1(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_503])).

tff(c_606,plain,(
    ! [A_170,B_171] :
      ( k4_tarski('#skF_4'(A_170,B_171),'#skF_5'(A_170,B_171)) = B_171
      | ~ r2_hidden(B_171,A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_676,plain,(
    ! [B_181,A_182] :
      ( k2_mcart_1(B_181) = '#skF_5'(A_182,B_181)
      | ~ r2_hidden(B_181,A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_46])).

tff(c_706,plain,(
    ! [A_183] :
      ( '#skF_5'(k1_tarski(A_183),A_183) = k2_mcart_1(A_183)
      | ~ v1_relat_1(k1_tarski(A_183)) ) ),
    inference(resolution,[status(thm)],[c_72,c_676])).

tff(c_719,plain,(
    '#skF_5'(k1_tarski('#skF_6'),'#skF_6') = k2_mcart_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_512,c_706])).

tff(c_723,plain,
    ( k4_tarski('#skF_4'(k1_tarski('#skF_6'),'#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ v1_relat_1(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_36])).

tff(c_727,plain,(
    k4_tarski('#skF_4'(k1_tarski('#skF_6'),'#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_72,c_723])).

tff(c_28,plain,(
    ! [B_11,D_13,A_10,C_12] :
      ( r2_hidden(B_11,D_13)
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_819,plain,(
    ! [D_195,C_196] :
      ( r2_hidden(k2_mcart_1('#skF_6'),D_195)
      | ~ r2_hidden('#skF_6',k2_zfmisc_1(C_196,D_195)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_28])).

tff(c_821,plain,(
    r2_hidden(k2_mcart_1('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_819])).

tff(c_825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.55  
% 2.86/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.86/1.55  
% 2.86/1.55  %Foreground sorts:
% 2.86/1.55  
% 2.86/1.55  
% 2.86/1.55  %Background operators:
% 2.86/1.55  
% 2.86/1.55  
% 2.86/1.55  %Foreground operators:
% 2.86/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.86/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.55  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.55  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.86/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.55  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.55  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.86/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.86/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.55  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.86/1.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.86/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.55  
% 2.96/1.56  tff(f_75, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.96/1.56  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.96/1.56  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.96/1.56  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.96/1.56  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.96/1.56  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.96/1.56  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.96/1.56  tff(f_68, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.96/1.56  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.96/1.56  tff(c_48, plain, (~r2_hidden(k2_mcart_1('#skF_6'), '#skF_8') | ~r2_hidden(k1_mcart_1('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.96/1.56  tff(c_90, plain, (~r2_hidden(k1_mcart_1('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_48])).
% 2.96/1.56  tff(c_50, plain, (r2_hidden('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.96/1.56  tff(c_24, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.96/1.56  tff(c_34, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.96/1.56  tff(c_103, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.56  tff(c_109, plain, (![A_64, A_65, B_66]: (v1_relat_1(A_64) | ~r1_tarski(A_64, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_34, c_103])).
% 2.96/1.56  tff(c_115, plain, (![A_67, A_68, B_69]: (v1_relat_1(k1_tarski(A_67)) | ~r2_hidden(A_67, k2_zfmisc_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_24, c_109])).
% 2.96/1.56  tff(c_124, plain, (v1_relat_1(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_115])).
% 2.96/1.56  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.96/1.56  tff(c_69, plain, (![D_42, B_43]: (r2_hidden(D_42, k2_tarski(D_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.96/1.56  tff(c_72, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_69])).
% 2.96/1.56  tff(c_159, plain, (![A_86, B_87]: (k4_tarski('#skF_4'(A_86, B_87), '#skF_5'(A_86, B_87))=B_87 | ~r2_hidden(B_87, A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.56  tff(c_46, plain, (![A_37, B_38]: (k2_mcart_1(k4_tarski(A_37, B_38))=B_38)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.96/1.56  tff(c_280, plain, (![B_105, A_106]: (k2_mcart_1(B_105)='#skF_5'(A_106, B_105) | ~r2_hidden(B_105, A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_159, c_46])).
% 2.96/1.56  tff(c_319, plain, (![A_110]: ('#skF_5'(k1_tarski(A_110), A_110)=k2_mcart_1(A_110) | ~v1_relat_1(k1_tarski(A_110)))), inference(resolution, [status(thm)], [c_72, c_280])).
% 2.96/1.56  tff(c_325, plain, ('#skF_5'(k1_tarski('#skF_6'), '#skF_6')=k2_mcart_1('#skF_6')), inference(resolution, [status(thm)], [c_124, c_319])).
% 2.96/1.56  tff(c_36, plain, (![A_16, B_31]: (k4_tarski('#skF_4'(A_16, B_31), '#skF_5'(A_16, B_31))=B_31 | ~r2_hidden(B_31, A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.56  tff(c_329, plain, (k4_tarski('#skF_4'(k1_tarski('#skF_6'), '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~r2_hidden('#skF_6', k1_tarski('#skF_6')) | ~v1_relat_1(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_325, c_36])).
% 2.96/1.56  tff(c_333, plain, (k4_tarski('#skF_4'(k1_tarski('#skF_6'), '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_72, c_329])).
% 2.96/1.56  tff(c_44, plain, (![A_37, B_38]: (k1_mcart_1(k4_tarski(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.96/1.56  tff(c_351, plain, ('#skF_4'(k1_tarski('#skF_6'), '#skF_6')=k1_mcart_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_333, c_44])).
% 2.96/1.56  tff(c_373, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_333])).
% 2.96/1.56  tff(c_30, plain, (![A_10, C_12, B_11, D_13]: (r2_hidden(A_10, C_12) | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.56  tff(c_470, plain, (![C_122, D_123]: (r2_hidden(k1_mcart_1('#skF_6'), C_122) | ~r2_hidden('#skF_6', k2_zfmisc_1(C_122, D_123)))), inference(superposition, [status(thm), theory('equality')], [c_373, c_30])).
% 2.96/1.56  tff(c_472, plain, (r2_hidden(k1_mcart_1('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_50, c_470])).
% 2.96/1.56  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_472])).
% 2.96/1.56  tff(c_477, plain, (~r2_hidden(k2_mcart_1('#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 2.96/1.56  tff(c_491, plain, (![C_132, A_133, B_134]: (v1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.56  tff(c_497, plain, (![A_135, A_136, B_137]: (v1_relat_1(A_135) | ~r1_tarski(A_135, k2_zfmisc_1(A_136, B_137)))), inference(resolution, [status(thm)], [c_34, c_491])).
% 2.96/1.56  tff(c_503, plain, (![A_138, A_139, B_140]: (v1_relat_1(k1_tarski(A_138)) | ~r2_hidden(A_138, k2_zfmisc_1(A_139, B_140)))), inference(resolution, [status(thm)], [c_24, c_497])).
% 2.96/1.56  tff(c_512, plain, (v1_relat_1(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_503])).
% 2.96/1.56  tff(c_606, plain, (![A_170, B_171]: (k4_tarski('#skF_4'(A_170, B_171), '#skF_5'(A_170, B_171))=B_171 | ~r2_hidden(B_171, A_170) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.56  tff(c_676, plain, (![B_181, A_182]: (k2_mcart_1(B_181)='#skF_5'(A_182, B_181) | ~r2_hidden(B_181, A_182) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_606, c_46])).
% 2.96/1.56  tff(c_706, plain, (![A_183]: ('#skF_5'(k1_tarski(A_183), A_183)=k2_mcart_1(A_183) | ~v1_relat_1(k1_tarski(A_183)))), inference(resolution, [status(thm)], [c_72, c_676])).
% 2.96/1.56  tff(c_719, plain, ('#skF_5'(k1_tarski('#skF_6'), '#skF_6')=k2_mcart_1('#skF_6')), inference(resolution, [status(thm)], [c_512, c_706])).
% 2.96/1.56  tff(c_723, plain, (k4_tarski('#skF_4'(k1_tarski('#skF_6'), '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~r2_hidden('#skF_6', k1_tarski('#skF_6')) | ~v1_relat_1(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_719, c_36])).
% 2.96/1.56  tff(c_727, plain, (k4_tarski('#skF_4'(k1_tarski('#skF_6'), '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_512, c_72, c_723])).
% 2.96/1.56  tff(c_28, plain, (![B_11, D_13, A_10, C_12]: (r2_hidden(B_11, D_13) | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.56  tff(c_819, plain, (![D_195, C_196]: (r2_hidden(k2_mcart_1('#skF_6'), D_195) | ~r2_hidden('#skF_6', k2_zfmisc_1(C_196, D_195)))), inference(superposition, [status(thm), theory('equality')], [c_727, c_28])).
% 2.96/1.56  tff(c_821, plain, (r2_hidden(k2_mcart_1('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_50, c_819])).
% 2.96/1.56  tff(c_825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_821])).
% 2.96/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.56  
% 2.96/1.56  Inference rules
% 2.96/1.56  ----------------------
% 2.96/1.56  #Ref     : 1
% 2.96/1.56  #Sup     : 197
% 2.96/1.56  #Fact    : 0
% 2.96/1.56  #Define  : 0
% 2.96/1.57  #Split   : 3
% 2.96/1.57  #Chain   : 0
% 2.96/1.57  #Close   : 0
% 2.96/1.57  
% 2.96/1.57  Ordering : KBO
% 2.96/1.57  
% 2.96/1.57  Simplification rules
% 2.96/1.57  ----------------------
% 2.96/1.57  #Subsume      : 23
% 2.96/1.57  #Demod        : 44
% 2.96/1.57  #Tautology    : 85
% 2.96/1.57  #SimpNegUnit  : 2
% 2.96/1.57  #BackRed      : 3
% 2.96/1.57  
% 2.96/1.57  #Partial instantiations: 0
% 2.96/1.57  #Strategies tried      : 1
% 2.96/1.57  
% 2.96/1.57  Timing (in seconds)
% 2.96/1.57  ----------------------
% 2.96/1.57  Preprocessing        : 0.33
% 2.96/1.57  Parsing              : 0.17
% 2.96/1.57  CNF conversion       : 0.02
% 2.96/1.57  Main loop            : 0.36
% 2.96/1.57  Inferencing          : 0.14
% 2.96/1.57  Reduction            : 0.11
% 2.96/1.57  Demodulation         : 0.08
% 2.96/1.57  BG Simplification    : 0.02
% 2.96/1.57  Subsumption          : 0.06
% 2.96/1.57  Abstraction          : 0.02
% 2.96/1.57  MUC search           : 0.00
% 2.96/1.57  Cooper               : 0.00
% 2.96/1.57  Total                : 0.71
% 2.96/1.57  Index Insertion      : 0.00
% 2.96/1.57  Index Deletion       : 0.00
% 2.96/1.57  Index Matching       : 0.00
% 2.96/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
