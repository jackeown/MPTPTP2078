%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   60 (  85 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 165 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_165,plain,(
    ! [A_95,C_96] :
      ( k1_funct_1(A_95,'#skF_4'(A_95,k2_relat_1(A_95),C_96)) = C_96
      | ~ r2_hidden(C_96,k2_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_132,plain,(
    ! [A_90,C_91] :
      ( r2_hidden('#skF_4'(A_90,k2_relat_1(A_90),C_91),k1_relat_1(A_90))
      | ~ r2_hidden(C_91,k2_relat_1(A_90))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_63,plain,(
    ! [B_68,A_69] :
      ( k7_relat_1(B_68,A_69) = B_68
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,
    ( k7_relat_1('#skF_8','#skF_6') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_63])).

tff(c_69,plain,(
    k7_relat_1('#skF_8','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_66])).

tff(c_79,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(A_73,B_74)
      | ~ r2_hidden(A_73,k1_relat_1(k7_relat_1(C_75,B_74)))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_73] :
      ( r2_hidden(A_73,'#skF_6')
      | ~ r2_hidden(A_73,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_79])).

tff(c_84,plain,(
    ! [A_73] :
      ( r2_hidden(A_73,'#skF_6')
      | ~ r2_hidden(A_73,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_82])).

tff(c_140,plain,(
    ! [C_91] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_91),'#skF_6')
      | ~ r2_hidden(C_91,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_132,c_84])).

tff(c_154,plain,(
    ! [C_92] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_92),'#skF_6')
      | ~ r2_hidden(C_92,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_46,c_140])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    ! [C_93] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_93),'#skF_6')
      | ~ r2_hidden(C_93,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_38,plain,(
    ! [E_58] :
      ( k1_funct_1('#skF_8',E_58) != '#skF_5'
      | ~ m1_subset_1(E_58,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_163,plain,(
    ! [C_93] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_93)) != '#skF_5'
      | ~ r2_hidden(C_93,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_159,c_38])).

tff(c_172,plain,(
    ! [C_96] :
      ( C_96 != '#skF_5'
      | ~ r2_hidden(C_96,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_96,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_163])).

tff(c_186,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_46,c_172])).

tff(c_92,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_96,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_92])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_98,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_40])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.21  
% 2.08/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.08/1.21  
% 2.08/1.21  %Foreground sorts:
% 2.08/1.21  
% 2.08/1.21  
% 2.08/1.21  %Background operators:
% 2.08/1.21  
% 2.08/1.21  
% 2.08/1.21  %Foreground operators:
% 2.08/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.08/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.08/1.21  tff('#skF_7', type, '#skF_7': $i).
% 2.08/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.08/1.21  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.08/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.08/1.21  tff('#skF_8', type, '#skF_8': $i).
% 2.08/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.08/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.21  
% 2.08/1.22  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.08/1.22  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.08/1.22  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.08/1.22  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.08/1.22  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.08/1.22  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.08/1.22  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.08/1.22  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.08/1.22  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.22  tff(c_53, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.22  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_53])).
% 2.08/1.22  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.22  tff(c_165, plain, (![A_95, C_96]: (k1_funct_1(A_95, '#skF_4'(A_95, k2_relat_1(A_95), C_96))=C_96 | ~r2_hidden(C_96, k2_relat_1(A_95)) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.22  tff(c_132, plain, (![A_90, C_91]: (r2_hidden('#skF_4'(A_90, k2_relat_1(A_90), C_91), k1_relat_1(A_90)) | ~r2_hidden(C_91, k2_relat_1(A_90)) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.22  tff(c_58, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.22  tff(c_62, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.08/1.22  tff(c_63, plain, (![B_68, A_69]: (k7_relat_1(B_68, A_69)=B_68 | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.22  tff(c_66, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_63])).
% 2.08/1.22  tff(c_69, plain, (k7_relat_1('#skF_8', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_66])).
% 2.08/1.22  tff(c_79, plain, (![A_73, B_74, C_75]: (r2_hidden(A_73, B_74) | ~r2_hidden(A_73, k1_relat_1(k7_relat_1(C_75, B_74))) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.22  tff(c_82, plain, (![A_73]: (r2_hidden(A_73, '#skF_6') | ~r2_hidden(A_73, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_79])).
% 2.08/1.22  tff(c_84, plain, (![A_73]: (r2_hidden(A_73, '#skF_6') | ~r2_hidden(A_73, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_82])).
% 2.08/1.22  tff(c_140, plain, (![C_91]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_91), '#skF_6') | ~r2_hidden(C_91, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_132, c_84])).
% 2.08/1.22  tff(c_154, plain, (![C_92]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_92), '#skF_6') | ~r2_hidden(C_92, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_46, c_140])).
% 2.08/1.22  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.22  tff(c_159, plain, (![C_93]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_93), '#skF_6') | ~r2_hidden(C_93, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_154, c_2])).
% 2.08/1.22  tff(c_38, plain, (![E_58]: (k1_funct_1('#skF_8', E_58)!='#skF_5' | ~m1_subset_1(E_58, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.22  tff(c_163, plain, (![C_93]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_93))!='#skF_5' | ~r2_hidden(C_93, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_159, c_38])).
% 2.08/1.22  tff(c_172, plain, (![C_96]: (C_96!='#skF_5' | ~r2_hidden(C_96, k2_relat_1('#skF_8')) | ~r2_hidden(C_96, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_163])).
% 2.08/1.22  tff(c_186, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_46, c_172])).
% 2.08/1.22  tff(c_92, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.22  tff(c_96, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_92])).
% 2.08/1.22  tff(c_40, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.22  tff(c_98, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_40])).
% 2.08/1.22  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_98])).
% 2.08/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.22  
% 2.08/1.22  Inference rules
% 2.08/1.22  ----------------------
% 2.08/1.22  #Ref     : 0
% 2.08/1.22  #Sup     : 29
% 2.08/1.22  #Fact    : 0
% 2.08/1.22  #Define  : 0
% 2.08/1.22  #Split   : 0
% 2.08/1.22  #Chain   : 0
% 2.08/1.22  #Close   : 0
% 2.08/1.22  
% 2.08/1.22  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 1
% 2.08/1.23  #Demod        : 11
% 2.08/1.23  #Tautology    : 12
% 2.08/1.23  #SimpNegUnit  : 1
% 2.08/1.23  #BackRed      : 3
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.32
% 2.08/1.23  Parsing              : 0.16
% 2.08/1.23  CNF conversion       : 0.03
% 2.08/1.23  Main loop            : 0.16
% 2.08/1.23  Inferencing          : 0.06
% 2.08/1.23  Reduction            : 0.05
% 2.08/1.23  Demodulation         : 0.04
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.03
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.51
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
