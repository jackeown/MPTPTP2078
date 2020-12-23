%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:17 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 104 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_73,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_73])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_128,plain,(
    ! [B_56,C_57,A_58] :
      ( r2_hidden(k1_funct_1(B_56,C_57),A_58)
      | ~ r2_hidden(C_57,k1_relat_1(B_56))
      | ~ v1_funct_1(B_56)
      | ~ v5_relat_1(B_56,A_58)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_135,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_38])).

tff(c_139,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_77,c_46,c_135])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_80,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_154,plain,(
    ! [B_64,A_65,C_66] :
      ( k1_xboole_0 = B_64
      | k1_relset_1(A_65,B_64,C_66) = A_65
      | ~ v1_funct_2(C_66,A_65,B_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_157,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_84,c_157])).

tff(c_161,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_160])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_181,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_4])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:55:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.17  
% 1.92/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.92/1.18  
% 1.92/1.18  %Foreground sorts:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Background operators:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Foreground operators:
% 1.92/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.92/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.92/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.92/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.92/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.18  
% 2.24/1.19  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.24/1.19  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.24/1.19  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.24/1.19  tff(f_45, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.24/1.19  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.19  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.24/1.19  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.24/1.19  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.19  tff(c_63, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.19  tff(c_67, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_63])).
% 2.24/1.19  tff(c_73, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.19  tff(c_77, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_73])).
% 2.24/1.19  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.19  tff(c_128, plain, (![B_56, C_57, A_58]: (r2_hidden(k1_funct_1(B_56, C_57), A_58) | ~r2_hidden(C_57, k1_relat_1(B_56)) | ~v1_funct_1(B_56) | ~v5_relat_1(B_56, A_58) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.19  tff(c_38, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.19  tff(c_135, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_38])).
% 2.24/1.19  tff(c_139, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_77, c_46, c_135])).
% 2.24/1.19  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.19  tff(c_44, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.19  tff(c_80, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.19  tff(c_84, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_80])).
% 2.24/1.19  tff(c_154, plain, (![B_64, A_65, C_66]: (k1_xboole_0=B_64 | k1_relset_1(A_65, B_64, C_66)=A_65 | ~v1_funct_2(C_66, A_65, B_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.19  tff(c_157, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_42, c_154])).
% 2.24/1.19  tff(c_160, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_84, c_157])).
% 2.24/1.19  tff(c_161, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_160])).
% 2.24/1.19  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.19  tff(c_181, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_4])).
% 2.24/1.19  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_181])).
% 2.24/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.19  
% 2.24/1.19  Inference rules
% 2.24/1.19  ----------------------
% 2.24/1.19  #Ref     : 0
% 2.24/1.19  #Sup     : 29
% 2.24/1.19  #Fact    : 0
% 2.24/1.19  #Define  : 0
% 2.24/1.19  #Split   : 0
% 2.24/1.19  #Chain   : 0
% 2.24/1.19  #Close   : 0
% 2.24/1.19  
% 2.24/1.19  Ordering : KBO
% 2.24/1.19  
% 2.24/1.19  Simplification rules
% 2.24/1.19  ----------------------
% 2.24/1.19  #Subsume      : 0
% 2.24/1.19  #Demod        : 19
% 2.24/1.19  #Tautology    : 11
% 2.24/1.19  #SimpNegUnit  : 2
% 2.24/1.19  #BackRed      : 4
% 2.24/1.19  
% 2.24/1.19  #Partial instantiations: 0
% 2.24/1.19  #Strategies tried      : 1
% 2.24/1.19  
% 2.24/1.19  Timing (in seconds)
% 2.24/1.19  ----------------------
% 2.24/1.19  Preprocessing        : 0.29
% 2.24/1.19  Parsing              : 0.15
% 2.24/1.19  CNF conversion       : 0.02
% 2.24/1.19  Main loop            : 0.17
% 2.24/1.19  Inferencing          : 0.06
% 2.24/1.19  Reduction            : 0.05
% 2.24/1.19  Demodulation         : 0.04
% 2.24/1.19  BG Simplification    : 0.01
% 2.24/1.19  Subsumption          : 0.04
% 2.24/1.19  Abstraction          : 0.01
% 2.24/1.19  MUC search           : 0.00
% 2.24/1.19  Cooper               : 0.00
% 2.24/1.19  Total                : 0.49
% 2.24/1.19  Index Insertion      : 0.00
% 2.24/1.19  Index Deletion       : 0.00
% 2.24/1.19  Index Matching       : 0.00
% 2.24/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
