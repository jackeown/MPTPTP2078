%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:08 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 116 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 353 expanded)
%              Number of equality atoms :   15 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_relset_1 > r1_tarski > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_relset_1,type,(
    r1_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( ! [E] : B != k1_tarski(E)
                & k5_partfun1(A,B,C) = k5_partfun1(A,B,D) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( r1_tarski(k5_partfun1(A,B,C),k5_partfun1(A,B,D))
              & ! [E] : B != k1_tarski(E) )
           => r1_relset_1(A,B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_relset_1(A,B,C,D)
      <=> r1_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    ! [A_28,B_29,D_30] :
      ( r2_relset_1(A_28,B_29,D_30,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [E_23] : k1_tarski(E_23) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    k5_partfun1('#skF_2','#skF_3','#skF_5') = k5_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_85,plain,(
    ! [A_45,B_46,D_47,C_48] :
      ( r1_relset_1(A_45,B_46,D_47,C_48)
      | k1_tarski('#skF_1'(A_45,B_46,C_48,D_47)) = B_46
      | ~ r1_tarski(k5_partfun1(A_45,B_46,C_48),k5_partfun1(A_45,B_46,D_47))
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_1(D_47)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_91,plain,(
    ! [C_48] :
      ( r1_relset_1('#skF_2','#skF_3','#skF_5',C_48)
      | k1_tarski('#skF_1'('#skF_2','#skF_3',C_48,'#skF_5')) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3',C_48),k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_100,plain,(
    ! [C_48] :
      ( r1_relset_1('#skF_2','#skF_3','#skF_5',C_48)
      | k1_tarski('#skF_1'('#skF_2','#skF_3',C_48,'#skF_5')) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3',C_48),k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_91])).

tff(c_126,plain,(
    ! [C_52] :
      ( r1_relset_1('#skF_2','#skF_3','#skF_5',C_52)
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3',C_52),k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_52) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_100])).

tff(c_133,plain,
    ( r1_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_138,plain,(
    r1_relset_1('#skF_2','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_133])).

tff(c_10,plain,(
    ! [C_5,D_6,A_3,B_4] :
      ( r1_tarski(C_5,D_6)
      | ~ r1_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_138,c_10])).

tff(c_143,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_140])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_147,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_88,plain,(
    ! [D_47] :
      ( r1_relset_1('#skF_2','#skF_3',D_47,'#skF_5')
      | k1_tarski('#skF_1'('#skF_2','#skF_3','#skF_5',D_47)) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3',D_47))
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_47)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_97,plain,(
    ! [D_47] :
      ( r1_relset_1('#skF_2','#skF_3',D_47,'#skF_5')
      | k1_tarski('#skF_1'('#skF_2','#skF_3','#skF_5',D_47)) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3',D_47))
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_88])).

tff(c_148,plain,(
    ! [D_53] :
      ( r1_relset_1('#skF_2','#skF_3',D_53,'#skF_5')
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3',D_53))
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_97])).

tff(c_155,plain,
    ( r1_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_160,plain,(
    r1_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_155])).

tff(c_162,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_160,c_10])).

tff(c_165,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_162])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_165])).

tff(c_168,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_178,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_18])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  %$ r2_relset_1 > r1_relset_1 > r1_tarski > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.05/1.26  
% 2.05/1.26  %Foreground sorts:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Background operators:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Foreground operators:
% 2.05/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.05/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.26  tff(r1_relset_1, type, r1_relset_1: ($i * $i * $i * $i) > $o).
% 2.05/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.05/1.26  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.05/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.26  
% 2.05/1.27  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((![E]: ~(B = k1_tarski(E))) & (k5_partfun1(A, B, C) = k5_partfun1(A, B, D))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_2)).
% 2.05/1.27  tff(f_45, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.05/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.05/1.27  tff(f_62, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r1_tarski(k5_partfun1(A, B, C), k5_partfun1(A, B, D)) & (![E]: ~(B = k1_tarski(E)))) => r1_relset_1(A, B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_2)).
% 2.05/1.27  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_relset_1(A, B, C, D) <=> r1_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_relset_1)).
% 2.05/1.27  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_45, plain, (![A_28, B_29, D_30]: (r2_relset_1(A_28, B_29, D_30, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.27  tff(c_50, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.05/1.27  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.27  tff(c_22, plain, (![E_23]: (k1_tarski(E_23)!='#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_20, plain, (k5_partfun1('#skF_2', '#skF_3', '#skF_5')=k5_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_85, plain, (![A_45, B_46, D_47, C_48]: (r1_relset_1(A_45, B_46, D_47, C_48) | k1_tarski('#skF_1'(A_45, B_46, C_48, D_47))=B_46 | ~r1_tarski(k5_partfun1(A_45, B_46, C_48), k5_partfun1(A_45, B_46, D_47)) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_1(D_47) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.27  tff(c_91, plain, (![C_48]: (r1_relset_1('#skF_2', '#skF_3', '#skF_5', C_48) | k1_tarski('#skF_1'('#skF_2', '#skF_3', C_48, '#skF_5'))='#skF_3' | ~r1_tarski(k5_partfun1('#skF_2', '#skF_3', C_48), k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_85])).
% 2.05/1.27  tff(c_100, plain, (![C_48]: (r1_relset_1('#skF_2', '#skF_3', '#skF_5', C_48) | k1_tarski('#skF_1'('#skF_2', '#skF_3', C_48, '#skF_5'))='#skF_3' | ~r1_tarski(k5_partfun1('#skF_2', '#skF_3', C_48), k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_48))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_91])).
% 2.05/1.27  tff(c_126, plain, (![C_52]: (r1_relset_1('#skF_2', '#skF_3', '#skF_5', C_52) | ~r1_tarski(k5_partfun1('#skF_2', '#skF_3', C_52), k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_52))), inference(negUnitSimplification, [status(thm)], [c_22, c_100])).
% 2.05/1.27  tff(c_133, plain, (r1_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_126])).
% 2.05/1.27  tff(c_138, plain, (r1_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_133])).
% 2.05/1.27  tff(c_10, plain, (![C_5, D_6, A_3, B_4]: (r1_tarski(C_5, D_6) | ~r1_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.27  tff(c_140, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_138, c_10])).
% 2.05/1.27  tff(c_143, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_140])).
% 2.05/1.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.27  tff(c_146, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_143, c_2])).
% 2.05/1.27  tff(c_147, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_146])).
% 2.05/1.27  tff(c_88, plain, (![D_47]: (r1_relset_1('#skF_2', '#skF_3', D_47, '#skF_5') | k1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5', D_47))='#skF_3' | ~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k5_partfun1('#skF_2', '#skF_3', D_47)) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(D_47) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_85])).
% 2.05/1.27  tff(c_97, plain, (![D_47]: (r1_relset_1('#skF_2', '#skF_3', D_47, '#skF_5') | k1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5', D_47))='#skF_3' | ~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k5_partfun1('#skF_2', '#skF_3', D_47)) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(D_47))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_88])).
% 2.05/1.27  tff(c_148, plain, (![D_53]: (r1_relset_1('#skF_2', '#skF_3', D_53, '#skF_5') | ~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k5_partfun1('#skF_2', '#skF_3', D_53)) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(D_53))), inference(negUnitSimplification, [status(thm)], [c_22, c_97])).
% 2.05/1.27  tff(c_155, plain, (r1_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.05/1.27  tff(c_160, plain, (r1_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_155])).
% 2.05/1.27  tff(c_162, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_160, c_10])).
% 2.05/1.27  tff(c_165, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_162])).
% 2.05/1.27  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_165])).
% 2.05/1.27  tff(c_168, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 2.05/1.27  tff(c_18, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.27  tff(c_178, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_18])).
% 2.05/1.27  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_178])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 25
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 1
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 1
% 2.05/1.27  #Demod        : 49
% 2.05/1.27  #Tautology    : 18
% 2.05/1.27  #SimpNegUnit  : 5
% 2.05/1.27  #BackRed      : 9
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.28  Preprocessing        : 0.30
% 2.05/1.28  Parsing              : 0.16
% 2.05/1.28  CNF conversion       : 0.02
% 2.05/1.28  Main loop            : 0.18
% 2.05/1.28  Inferencing          : 0.06
% 2.05/1.28  Reduction            : 0.06
% 2.05/1.28  Demodulation         : 0.05
% 2.05/1.28  BG Simplification    : 0.01
% 2.05/1.28  Subsumption          : 0.04
% 2.05/1.28  Abstraction          : 0.01
% 2.05/1.28  MUC search           : 0.00
% 2.05/1.28  Cooper               : 0.00
% 2.05/1.28  Total                : 0.51
% 2.05/1.28  Index Insertion      : 0.00
% 2.05/1.28  Index Deletion       : 0.00
% 2.05/1.28  Index Matching       : 0.00
% 2.05/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
