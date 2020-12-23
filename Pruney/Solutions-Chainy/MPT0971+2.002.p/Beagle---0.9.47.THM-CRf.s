%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 103 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 243 expanded)
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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_53,axiom,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_67,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    v4_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_5'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [A_99,C_100] :
      ( r2_hidden('#skF_5'(A_99,k2_relat_1(A_99),C_100),k1_relat_1(A_99))
      | ~ r2_hidden(C_100,k2_relat_1(A_99))
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_254,plain,(
    ! [A_127,C_128,B_129] :
      ( r2_hidden('#skF_5'(A_127,k2_relat_1(A_127),C_128),B_129)
      | ~ r1_tarski(k1_relat_1(A_127),B_129)
      | ~ r2_hidden(C_128,k2_relat_1(A_127))
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_38,plain,(
    ! [E_58] :
      ( k1_funct_1('#skF_9',E_58) != '#skF_8'
      | ~ r2_hidden(E_58,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_296,plain,(
    ! [A_132,C_133] :
      ( k1_funct_1('#skF_9','#skF_5'(A_132,k2_relat_1(A_132),C_133)) != '#skF_8'
      | ~ r1_tarski(k1_relat_1(A_132),'#skF_6')
      | ~ r2_hidden(C_133,k2_relat_1(A_132))
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_254,c_38])).

tff(c_300,plain,(
    ! [C_44] :
      ( C_44 != '#skF_8'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_296])).

tff(c_302,plain,(
    ! [C_44] :
      ( C_44 != '#skF_8'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_52,c_46,c_300])).

tff(c_303,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_306,plain,
    ( ~ v4_relat_1('#skF_9','#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_306])).

tff(c_326,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_117,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_40,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_123,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_40])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.82/1.37  
% 2.82/1.37  %Foreground sorts:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Background operators:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Foreground operators:
% 2.82/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.82/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.82/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.82/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.82/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.37  
% 2.82/1.39  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.82/1.39  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.39  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.39  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.82/1.39  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.82/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.82/1.39  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.82/1.39  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.39  tff(c_48, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.39  tff(c_52, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_48])).
% 2.82/1.39  tff(c_67, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.82/1.39  tff(c_71, plain, (v4_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_67])).
% 2.82/1.39  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.39  tff(c_46, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.39  tff(c_14, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_5'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.39  tff(c_150, plain, (![A_99, C_100]: (r2_hidden('#skF_5'(A_99, k2_relat_1(A_99), C_100), k1_relat_1(A_99)) | ~r2_hidden(C_100, k2_relat_1(A_99)) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.39  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.39  tff(c_254, plain, (![A_127, C_128, B_129]: (r2_hidden('#skF_5'(A_127, k2_relat_1(A_127), C_128), B_129) | ~r1_tarski(k1_relat_1(A_127), B_129) | ~r2_hidden(C_128, k2_relat_1(A_127)) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_150, c_2])).
% 2.82/1.39  tff(c_38, plain, (![E_58]: (k1_funct_1('#skF_9', E_58)!='#skF_8' | ~r2_hidden(E_58, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.39  tff(c_296, plain, (![A_132, C_133]: (k1_funct_1('#skF_9', '#skF_5'(A_132, k2_relat_1(A_132), C_133))!='#skF_8' | ~r1_tarski(k1_relat_1(A_132), '#skF_6') | ~r2_hidden(C_133, k2_relat_1(A_132)) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_254, c_38])).
% 2.82/1.39  tff(c_300, plain, (![C_44]: (C_44!='#skF_8' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(C_44, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_44, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_296])).
% 2.82/1.39  tff(c_302, plain, (![C_44]: (C_44!='#skF_8' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(C_44, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_52, c_46, c_300])).
% 2.82/1.39  tff(c_303, plain, (~r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_302])).
% 2.82/1.39  tff(c_306, plain, (~v4_relat_1('#skF_9', '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_10, c_303])).
% 2.82/1.39  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_306])).
% 2.82/1.39  tff(c_326, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_302])).
% 2.82/1.39  tff(c_117, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.82/1.39  tff(c_121, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_117])).
% 2.82/1.39  tff(c_40, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.39  tff(c_123, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_40])).
% 2.82/1.39  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_326, c_123])).
% 2.82/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  Inference rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Ref     : 0
% 2.82/1.39  #Sup     : 59
% 2.82/1.39  #Fact    : 0
% 2.82/1.39  #Define  : 0
% 2.82/1.39  #Split   : 1
% 2.82/1.39  #Chain   : 0
% 2.82/1.39  #Close   : 0
% 2.82/1.39  
% 2.82/1.39  Ordering : KBO
% 2.82/1.39  
% 2.82/1.39  Simplification rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Subsume      : 5
% 2.82/1.39  #Demod        : 12
% 2.82/1.39  #Tautology    : 12
% 2.82/1.39  #SimpNegUnit  : 1
% 2.82/1.39  #BackRed      : 3
% 2.82/1.39  
% 2.82/1.39  #Partial instantiations: 0
% 2.82/1.39  #Strategies tried      : 1
% 2.82/1.39  
% 2.82/1.39  Timing (in seconds)
% 2.82/1.39  ----------------------
% 2.82/1.39  Preprocessing        : 0.33
% 2.82/1.39  Parsing              : 0.16
% 2.82/1.39  CNF conversion       : 0.03
% 2.82/1.39  Main loop            : 0.29
% 2.82/1.39  Inferencing          : 0.11
% 2.82/1.39  Reduction            : 0.07
% 2.82/1.39  Demodulation         : 0.05
% 2.82/1.39  BG Simplification    : 0.02
% 2.82/1.39  Subsumption          : 0.06
% 2.82/1.39  Abstraction          : 0.02
% 2.82/1.39  MUC search           : 0.00
% 2.82/1.39  Cooper               : 0.00
% 2.82/1.39  Total                : 0.65
% 2.82/1.39  Index Insertion      : 0.00
% 2.82/1.39  Index Deletion       : 0.00
% 2.82/1.39  Index Matching       : 0.00
% 2.82/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
