%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 169 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_55])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_11,C_47] :
      ( k1_funct_1(A_11,'#skF_4'(A_11,k2_relat_1(A_11),C_47)) = C_47
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_11,C_47] :
      ( r2_hidden('#skF_4'(A_11,k2_relat_1(A_11),C_47),k1_relat_1(A_11))
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_124,plain,(
    ! [A_102,C_103] :
      ( r2_hidden(k4_tarski(A_102,k1_funct_1(C_103,A_102)),C_103)
      | ~ r2_hidden(A_102,k1_relat_1(C_103))
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_334,plain,(
    ! [A_137,C_138,A_139] :
      ( r2_hidden(k4_tarski(A_137,k1_funct_1(C_138,A_137)),A_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_139))
      | ~ r2_hidden(A_137,k1_relat_1(C_138))
      | ~ v1_funct_1(C_138)
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_371,plain,(
    ! [A_140,C_141,C_142,D_143] :
      ( r2_hidden(A_140,C_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(C_141,D_143)))
      | ~ r2_hidden(A_140,k1_relat_1(C_142))
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_334,c_6])).

tff(c_382,plain,(
    ! [A_140] :
      ( r2_hidden(A_140,'#skF_6')
      | ~ r2_hidden(A_140,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_371])).

tff(c_390,plain,(
    ! [A_147] :
      ( r2_hidden(A_147,'#skF_6')
      | ~ r2_hidden(A_147,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48,c_382])).

tff(c_422,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_47),'#skF_6')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16,c_390])).

tff(c_442,plain,(
    ! [C_148] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_148),'#skF_6')
      | ~ r2_hidden(C_148,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48,c_422])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_450,plain,(
    ! [C_149] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_149),'#skF_6')
      | ~ r2_hidden(C_149,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_442,c_10])).

tff(c_40,plain,(
    ! [E_61] :
      ( k1_funct_1('#skF_8',E_61) != '#skF_5'
      | ~ m1_subset_1(E_61,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_455,plain,(
    ! [C_150] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_150)) != '#skF_5'
      | ~ r2_hidden(C_150,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_450,c_40])).

tff(c_459,plain,(
    ! [C_47] :
      ( C_47 != '#skF_5'
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_455])).

tff(c_462,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48,c_459])).

tff(c_67,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_71,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_74,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_42])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.93  
% 3.47/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.93  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 3.47/1.93  
% 3.47/1.93  %Foreground sorts:
% 3.47/1.93  
% 3.47/1.93  
% 3.47/1.93  %Background operators:
% 3.47/1.93  
% 3.47/1.93  
% 3.47/1.93  %Foreground operators:
% 3.47/1.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.47/1.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.47/1.93  tff('#skF_7', type, '#skF_7': $i).
% 3.47/1.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.47/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.93  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.93  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.47/1.93  tff('#skF_8', type, '#skF_8': $i).
% 3.47/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.93  
% 3.47/1.95  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.47/1.95  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.47/1.95  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.47/1.95  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.47/1.95  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.47/1.95  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.47/1.95  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.47/1.95  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.47/1.95  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.47/1.95  tff(c_55, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.95  tff(c_59, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_55])).
% 3.47/1.95  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.47/1.95  tff(c_14, plain, (![A_11, C_47]: (k1_funct_1(A_11, '#skF_4'(A_11, k2_relat_1(A_11), C_47))=C_47 | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.95  tff(c_16, plain, (![A_11, C_47]: (r2_hidden('#skF_4'(A_11, k2_relat_1(A_11), C_47), k1_relat_1(A_11)) | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.95  tff(c_124, plain, (![A_102, C_103]: (r2_hidden(k4_tarski(A_102, k1_funct_1(C_103, A_102)), C_103) | ~r2_hidden(A_102, k1_relat_1(C_103)) | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.47/1.95  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.95  tff(c_334, plain, (![A_137, C_138, A_139]: (r2_hidden(k4_tarski(A_137, k1_funct_1(C_138, A_137)), A_139) | ~m1_subset_1(C_138, k1_zfmisc_1(A_139)) | ~r2_hidden(A_137, k1_relat_1(C_138)) | ~v1_funct_1(C_138) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_124, c_8])).
% 3.47/1.95  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.95  tff(c_371, plain, (![A_140, C_141, C_142, D_143]: (r2_hidden(A_140, C_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(C_141, D_143))) | ~r2_hidden(A_140, k1_relat_1(C_142)) | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_334, c_6])).
% 3.47/1.95  tff(c_382, plain, (![A_140]: (r2_hidden(A_140, '#skF_6') | ~r2_hidden(A_140, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_371])).
% 3.47/1.95  tff(c_390, plain, (![A_147]: (r2_hidden(A_147, '#skF_6') | ~r2_hidden(A_147, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_48, c_382])).
% 3.47/1.95  tff(c_422, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_47), '#skF_6') | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16, c_390])).
% 3.47/1.95  tff(c_442, plain, (![C_148]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_148), '#skF_6') | ~r2_hidden(C_148, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_48, c_422])).
% 3.47/1.95  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.47/1.95  tff(c_450, plain, (![C_149]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_149), '#skF_6') | ~r2_hidden(C_149, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_442, c_10])).
% 3.47/1.95  tff(c_40, plain, (![E_61]: (k1_funct_1('#skF_8', E_61)!='#skF_5' | ~m1_subset_1(E_61, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.47/1.95  tff(c_455, plain, (![C_150]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_150))!='#skF_5' | ~r2_hidden(C_150, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_450, c_40])).
% 3.47/1.95  tff(c_459, plain, (![C_47]: (C_47!='#skF_5' | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_455])).
% 3.47/1.95  tff(c_462, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_48, c_459])).
% 3.47/1.95  tff(c_67, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.47/1.95  tff(c_71, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.47/1.95  tff(c_42, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.47/1.95  tff(c_74, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_42])).
% 3.47/1.95  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_462, c_74])).
% 3.47/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.96  
% 3.47/1.96  Inference rules
% 3.47/1.96  ----------------------
% 3.47/1.96  #Ref     : 0
% 3.47/1.96  #Sup     : 89
% 3.47/1.96  #Fact    : 0
% 3.47/1.96  #Define  : 0
% 3.47/1.96  #Split   : 1
% 3.47/1.96  #Chain   : 0
% 3.47/1.96  #Close   : 0
% 3.47/1.96  
% 3.47/1.96  Ordering : KBO
% 3.47/1.96  
% 3.47/1.96  Simplification rules
% 3.47/1.96  ----------------------
% 3.47/1.96  #Subsume      : 3
% 3.47/1.96  #Demod        : 14
% 3.47/1.96  #Tautology    : 12
% 3.47/1.96  #SimpNegUnit  : 1
% 3.47/1.96  #BackRed      : 4
% 3.47/1.96  
% 3.47/1.96  #Partial instantiations: 0
% 3.47/1.96  #Strategies tried      : 1
% 3.47/1.96  
% 3.47/1.96  Timing (in seconds)
% 3.47/1.96  ----------------------
% 3.47/1.96  Preprocessing        : 0.51
% 3.47/1.96  Parsing              : 0.25
% 3.47/1.96  CNF conversion       : 0.04
% 3.47/1.96  Main loop            : 0.50
% 3.47/1.96  Inferencing          : 0.19
% 3.47/1.96  Reduction            : 0.13
% 3.47/1.96  Demodulation         : 0.09
% 3.47/1.96  BG Simplification    : 0.04
% 3.47/1.96  Subsumption          : 0.10
% 3.47/1.96  Abstraction          : 0.03
% 3.47/1.96  MUC search           : 0.00
% 3.47/1.96  Cooper               : 0.00
% 3.47/1.96  Total                : 1.05
% 3.47/1.96  Index Insertion      : 0.00
% 3.47/1.96  Index Deletion       : 0.00
% 3.47/1.96  Index Matching       : 0.00
% 3.47/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
