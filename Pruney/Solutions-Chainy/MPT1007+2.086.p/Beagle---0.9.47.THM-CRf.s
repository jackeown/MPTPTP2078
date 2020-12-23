%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:22 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 114 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_30,C_31,B_32] :
      ( r2_hidden(A_30,C_31)
      | ~ r1_tarski(k2_tarski(A_30,B_32),C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_36,B_37] : r2_hidden(A_36,k2_tarski(A_36,B_37)) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_78,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_169,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_173,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_169])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k2_relset_1(A_16,B_17,C_18),k1_zfmisc_1(B_17))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_183,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_22])).

tff(c_187,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_183])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_196,plain,(
    ! [D_74,C_75,A_76,B_77] :
      ( r2_hidden(k1_funct_1(D_74,C_75),k2_relset_1(A_76,B_77,D_74))
      | k1_xboole_0 = B_77
      | ~ r2_hidden(C_75,A_76)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_2(D_74,A_76,B_77)
      | ~ v1_funct_1(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_201,plain,(
    ! [C_75] :
      ( r2_hidden(k1_funct_1('#skF_3',C_75),k2_relat_1('#skF_3'))
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_75,k1_tarski('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')))
      | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_196])).

tff(c_204,plain,(
    ! [C_75] :
      ( r2_hidden(k1_funct_1('#skF_3',C_75),k2_relat_1('#skF_3'))
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_75,k1_tarski('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_201])).

tff(c_206,plain,(
    ! [C_78] :
      ( r2_hidden(k1_funct_1('#skF_3',C_78),k2_relat_1('#skF_3'))
      | ~ r2_hidden(C_78,k1_tarski('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_204])).

tff(c_20,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(k1_funct_1('#skF_3',C_79),A_80)
      | ~ m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(A_80))
      | ~ r2_hidden(C_79,k1_tarski('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_206,c_20])).

tff(c_214,plain,(
    ! [C_81] :
      ( r2_hidden(k1_funct_1('#skF_3',C_81),'#skF_2')
      | ~ r2_hidden(C_81,k1_tarski('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_187,c_210])).

tff(c_28,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_219,plain,(
    ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_214,c_28])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.32  
% 2.14/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.32  
% 2.14/1.32  %Foreground sorts:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Background operators:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Foreground operators:
% 2.14/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.14/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.32  
% 2.14/1.34  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.34  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.34  tff(f_82, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.14/1.34  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.14/1.34  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.14/1.34  tff(f_70, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.14/1.34  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.14/1.34  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.34  tff(c_57, plain, (![A_30, C_31, B_32]: (r2_hidden(A_30, C_31) | ~r1_tarski(k2_tarski(A_30, B_32), C_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.34  tff(c_75, plain, (![A_36, B_37]: (r2_hidden(A_36, k2_tarski(A_36, B_37)))), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.14/1.34  tff(c_78, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 2.14/1.34  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.14/1.34  tff(c_169, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.34  tff(c_173, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_169])).
% 2.14/1.34  tff(c_22, plain, (![A_16, B_17, C_18]: (m1_subset_1(k2_relset_1(A_16, B_17, C_18), k1_zfmisc_1(B_17)) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.34  tff(c_183, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_173, c_22])).
% 2.14/1.34  tff(c_187, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_183])).
% 2.14/1.34  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.14/1.34  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.14/1.34  tff(c_34, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.14/1.34  tff(c_196, plain, (![D_74, C_75, A_76, B_77]: (r2_hidden(k1_funct_1(D_74, C_75), k2_relset_1(A_76, B_77, D_74)) | k1_xboole_0=B_77 | ~r2_hidden(C_75, A_76) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_2(D_74, A_76, B_77) | ~v1_funct_1(D_74))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.34  tff(c_201, plain, (![C_75]: (r2_hidden(k1_funct_1('#skF_3', C_75), k2_relat_1('#skF_3')) | k1_xboole_0='#skF_2' | ~r2_hidden(C_75, k1_tarski('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_196])).
% 2.14/1.34  tff(c_204, plain, (![C_75]: (r2_hidden(k1_funct_1('#skF_3', C_75), k2_relat_1('#skF_3')) | k1_xboole_0='#skF_2' | ~r2_hidden(C_75, k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_201])).
% 2.14/1.34  tff(c_206, plain, (![C_78]: (r2_hidden(k1_funct_1('#skF_3', C_78), k2_relat_1('#skF_3')) | ~r2_hidden(C_78, k1_tarski('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_204])).
% 2.14/1.34  tff(c_20, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.34  tff(c_210, plain, (![C_79, A_80]: (r2_hidden(k1_funct_1('#skF_3', C_79), A_80) | ~m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1(A_80)) | ~r2_hidden(C_79, k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_206, c_20])).
% 2.14/1.34  tff(c_214, plain, (![C_81]: (r2_hidden(k1_funct_1('#skF_3', C_81), '#skF_2') | ~r2_hidden(C_81, k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_187, c_210])).
% 2.14/1.34  tff(c_28, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.14/1.34  tff(c_219, plain, (~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_214, c_28])).
% 2.14/1.34  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_219])).
% 2.14/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.34  
% 2.14/1.34  Inference rules
% 2.14/1.34  ----------------------
% 2.14/1.34  #Ref     : 0
% 2.14/1.34  #Sup     : 40
% 2.14/1.34  #Fact    : 0
% 2.14/1.34  #Define  : 0
% 2.14/1.34  #Split   : 0
% 2.14/1.34  #Chain   : 0
% 2.14/1.34  #Close   : 0
% 2.14/1.34  
% 2.14/1.34  Ordering : KBO
% 2.14/1.34  
% 2.14/1.34  Simplification rules
% 2.14/1.34  ----------------------
% 2.14/1.34  #Subsume      : 3
% 2.14/1.34  #Demod        : 11
% 2.14/1.34  #Tautology    : 17
% 2.14/1.34  #SimpNegUnit  : 1
% 2.14/1.34  #BackRed      : 0
% 2.14/1.34  
% 2.14/1.34  #Partial instantiations: 0
% 2.14/1.34  #Strategies tried      : 1
% 2.14/1.34  
% 2.14/1.34  Timing (in seconds)
% 2.14/1.34  ----------------------
% 2.14/1.34  Preprocessing        : 0.38
% 2.14/1.34  Parsing              : 0.21
% 2.14/1.34  CNF conversion       : 0.02
% 2.14/1.34  Main loop            : 0.20
% 2.14/1.34  Inferencing          : 0.08
% 2.14/1.34  Reduction            : 0.06
% 2.14/1.34  Demodulation         : 0.05
% 2.14/1.34  BG Simplification    : 0.01
% 2.14/1.34  Subsumption          : 0.04
% 2.14/1.34  Abstraction          : 0.01
% 2.14/1.34  MUC search           : 0.00
% 2.14/1.34  Cooper               : 0.00
% 2.14/1.34  Total                : 0.61
% 2.14/1.34  Index Insertion      : 0.00
% 2.14/1.34  Index Deletion       : 0.00
% 2.14/1.34  Index Matching       : 0.00
% 2.14/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
