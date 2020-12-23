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

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 108 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 257 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_67,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_80,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_179,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_4'(A_115,k2_relat_1(A_115),C_116),k1_relat_1(A_115))
      | ~ r2_hidden(C_116,k2_relat_1(A_115))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_86,C_87,B_88] :
      ( m1_subset_1(A_86,C_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(C_87))
      | ~ r2_hidden(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_86,B_2,A_1] :
      ( m1_subset_1(A_86,B_2)
      | ~ r2_hidden(A_86,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_222,plain,(
    ! [A_128,C_129,B_130] :
      ( m1_subset_1('#skF_4'(A_128,k2_relat_1(A_128),C_129),B_130)
      | ~ r1_tarski(k1_relat_1(A_128),B_130)
      | ~ r2_hidden(C_129,k2_relat_1(A_128))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_179,c_132])).

tff(c_38,plain,(
    ! [E_58] :
      ( k1_funct_1('#skF_8',E_58) != '#skF_5'
      | ~ m1_subset_1(E_58,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_258,plain,(
    ! [A_134,C_135] :
      ( k1_funct_1('#skF_8','#skF_4'(A_134,k2_relat_1(A_134),C_135)) != '#skF_5'
      | ~ r1_tarski(k1_relat_1(A_134),'#skF_6')
      | ~ r2_hidden(C_135,k2_relat_1(A_134))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_222,c_38])).

tff(c_262,plain,(
    ! [C_44] :
      ( C_44 != '#skF_5'
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_258])).

tff(c_264,plain,(
    ! [C_44] :
      ( C_44 != '#skF_5'
      | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_46,c_67,c_46,c_262])).

tff(c_265,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_268,plain,
    ( ~ v4_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_265])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_89,c_268])).

tff(c_282,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_142,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_151,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_142])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_153,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_40])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_153])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.41  
% 2.33/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.33/1.41  
% 2.33/1.41  %Foreground sorts:
% 2.33/1.41  
% 2.33/1.41  
% 2.33/1.41  %Background operators:
% 2.33/1.41  
% 2.33/1.41  
% 2.33/1.41  %Foreground operators:
% 2.33/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.33/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.33/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.33/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.33/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.33/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.33/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.33/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.33/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.33/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.33/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.41  
% 2.33/1.42  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.33/1.42  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.33/1.42  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/1.42  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.33/1.42  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.33/1.42  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.42  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.33/1.42  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.33/1.42  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.33/1.42  tff(c_58, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.42  tff(c_67, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.33/1.42  tff(c_80, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.42  tff(c_89, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_80])).
% 2.33/1.42  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.42  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.33/1.42  tff(c_14, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_4'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.42  tff(c_179, plain, (![A_115, C_116]: (r2_hidden('#skF_4'(A_115, k2_relat_1(A_115), C_116), k1_relat_1(A_115)) | ~r2_hidden(C_116, k2_relat_1(A_115)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.42  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.42  tff(c_127, plain, (![A_86, C_87, B_88]: (m1_subset_1(A_86, C_87) | ~m1_subset_1(B_88, k1_zfmisc_1(C_87)) | ~r2_hidden(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.42  tff(c_132, plain, (![A_86, B_2, A_1]: (m1_subset_1(A_86, B_2) | ~r2_hidden(A_86, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_127])).
% 2.33/1.42  tff(c_222, plain, (![A_128, C_129, B_130]: (m1_subset_1('#skF_4'(A_128, k2_relat_1(A_128), C_129), B_130) | ~r1_tarski(k1_relat_1(A_128), B_130) | ~r2_hidden(C_129, k2_relat_1(A_128)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_179, c_132])).
% 2.33/1.42  tff(c_38, plain, (![E_58]: (k1_funct_1('#skF_8', E_58)!='#skF_5' | ~m1_subset_1(E_58, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.33/1.42  tff(c_258, plain, (![A_134, C_135]: (k1_funct_1('#skF_8', '#skF_4'(A_134, k2_relat_1(A_134), C_135))!='#skF_5' | ~r1_tarski(k1_relat_1(A_134), '#skF_6') | ~r2_hidden(C_135, k2_relat_1(A_134)) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_222, c_38])).
% 2.33/1.42  tff(c_262, plain, (![C_44]: (C_44!='#skF_5' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_258])).
% 2.33/1.42  tff(c_264, plain, (![C_44]: (C_44!='#skF_5' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~r2_hidden(C_44, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_46, c_67, c_46, c_262])).
% 2.33/1.42  tff(c_265, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_264])).
% 2.33/1.42  tff(c_268, plain, (~v4_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10, c_265])).
% 2.33/1.43  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_89, c_268])).
% 2.33/1.43  tff(c_282, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_264])).
% 2.33/1.43  tff(c_142, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.33/1.43  tff(c_151, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_142])).
% 2.33/1.43  tff(c_40, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.33/1.43  tff(c_153, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_40])).
% 2.33/1.43  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_153])).
% 2.33/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.43  
% 2.33/1.43  Inference rules
% 2.33/1.43  ----------------------
% 2.33/1.43  #Ref     : 0
% 2.33/1.43  #Sup     : 47
% 2.33/1.43  #Fact    : 0
% 2.33/1.43  #Define  : 0
% 2.33/1.43  #Split   : 1
% 2.33/1.43  #Chain   : 0
% 2.33/1.43  #Close   : 0
% 2.33/1.43  
% 2.33/1.43  Ordering : KBO
% 2.33/1.43  
% 2.33/1.43  Simplification rules
% 2.33/1.43  ----------------------
% 2.33/1.43  #Subsume      : 1
% 2.33/1.43  #Demod        : 14
% 2.33/1.43  #Tautology    : 14
% 2.33/1.43  #SimpNegUnit  : 1
% 2.33/1.43  #BackRed      : 3
% 2.33/1.43  
% 2.33/1.43  #Partial instantiations: 0
% 2.33/1.43  #Strategies tried      : 1
% 2.33/1.43  
% 2.33/1.43  Timing (in seconds)
% 2.33/1.43  ----------------------
% 2.33/1.43  Preprocessing        : 0.37
% 2.33/1.43  Parsing              : 0.19
% 2.33/1.43  CNF conversion       : 0.03
% 2.33/1.43  Main loop            : 0.22
% 2.33/1.43  Inferencing          : 0.09
% 2.33/1.43  Reduction            : 0.05
% 2.33/1.43  Demodulation         : 0.04
% 2.33/1.43  BG Simplification    : 0.02
% 2.33/1.43  Subsumption          : 0.04
% 2.33/1.43  Abstraction          : 0.01
% 2.33/1.43  MUC search           : 0.00
% 2.33/1.43  Cooper               : 0.00
% 2.33/1.43  Total                : 0.61
% 2.33/1.43  Index Insertion      : 0.00
% 2.33/1.43  Index Deletion       : 0.00
% 2.33/1.43  Index Matching       : 0.00
% 2.33/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
