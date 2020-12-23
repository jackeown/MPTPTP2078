%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:37 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 135 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_20,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    ! [C_35,B_36,A_37] :
      ( ~ v1_xboole_0(C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [A_9,A_37] :
      ( ~ v1_xboole_0(A_9)
      | ~ r2_hidden(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_72,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_84,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_94,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_90])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_95,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36])).

tff(c_117,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_117])).

tff(c_141,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_133])).

tff(c_142,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_141])).

tff(c_604,plain,(
    ! [B_83,A_84] :
      ( ~ v1_subset_1(B_83,A_84)
      | v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_zfmisc_1(A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_616,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_604])).

tff(c_632,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_616])).

tff(c_633,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_632])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(B_30)
      | B_30 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_672,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_633,c_55])).

tff(c_8,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_694,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_8])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_694])).

tff(c_699,plain,(
    ! [A_9] : ~ v1_xboole_0(A_9) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.45  
% 3.05/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.45  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.05/1.45  
% 3.05/1.45  %Foreground sorts:
% 3.05/1.45  
% 3.05/1.45  
% 3.05/1.45  %Background operators:
% 3.05/1.45  
% 3.05/1.45  
% 3.05/1.45  %Foreground operators:
% 3.05/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.05/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.05/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.05/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.45  
% 3.05/1.46  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.05/1.46  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.05/1.46  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.05/1.46  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.05/1.46  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.05/1.46  tff(f_94, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.05/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.05/1.46  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.05/1.46  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.05/1.46  tff(c_20, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.05/1.46  tff(c_68, plain, (![C_35, B_36, A_37]: (~v1_xboole_0(C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.05/1.46  tff(c_71, plain, (![A_9, A_37]: (~v1_xboole_0(A_9) | ~r2_hidden(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_68])).
% 3.05/1.46  tff(c_72, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_71])).
% 3.05/1.46  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.05/1.46  tff(c_34, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.05/1.46  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.05/1.46  tff(c_84, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.05/1.46  tff(c_90, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_84])).
% 3.05/1.46  tff(c_94, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_90])).
% 3.05/1.46  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.05/1.46  tff(c_95, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36])).
% 3.05/1.46  tff(c_117, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.05/1.46  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_94, c_117])).
% 3.05/1.46  tff(c_141, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_133])).
% 3.05/1.46  tff(c_142, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_141])).
% 3.05/1.46  tff(c_604, plain, (![B_83, A_84]: (~v1_subset_1(B_83, A_84) | v1_xboole_0(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_zfmisc_1(A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.05/1.46  tff(c_616, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_142, c_604])).
% 3.05/1.46  tff(c_632, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95, c_616])).
% 3.05/1.46  tff(c_633, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_632])).
% 3.05/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.05/1.46  tff(c_52, plain, (![B_30, A_31]: (~v1_xboole_0(B_30) | B_30=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.05/1.46  tff(c_55, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_2, c_52])).
% 3.05/1.46  tff(c_672, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_633, c_55])).
% 3.05/1.46  tff(c_8, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.46  tff(c_694, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_672, c_8])).
% 3.05/1.46  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_694])).
% 3.05/1.46  tff(c_699, plain, (![A_9]: (~v1_xboole_0(A_9))), inference(splitRight, [status(thm)], [c_71])).
% 3.05/1.46  tff(c_701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_699, c_2])).
% 3.05/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.46  
% 3.05/1.46  Inference rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Ref     : 0
% 3.05/1.46  #Sup     : 146
% 3.05/1.46  #Fact    : 0
% 3.05/1.46  #Define  : 0
% 3.05/1.46  #Split   : 2
% 3.05/1.46  #Chain   : 0
% 3.05/1.46  #Close   : 0
% 3.05/1.46  
% 3.05/1.46  Ordering : KBO
% 3.05/1.46  
% 3.05/1.46  Simplification rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Subsume      : 34
% 3.05/1.46  #Demod        : 75
% 3.05/1.46  #Tautology    : 61
% 3.05/1.46  #SimpNegUnit  : 16
% 3.05/1.46  #BackRed      : 19
% 3.05/1.46  
% 3.05/1.46  #Partial instantiations: 0
% 3.05/1.46  #Strategies tried      : 1
% 3.05/1.46  
% 3.05/1.46  Timing (in seconds)
% 3.05/1.46  ----------------------
% 3.05/1.47  Preprocessing        : 0.34
% 3.05/1.47  Parsing              : 0.18
% 3.05/1.47  CNF conversion       : 0.03
% 3.05/1.47  Main loop            : 0.33
% 3.05/1.47  Inferencing          : 0.12
% 3.05/1.47  Reduction            : 0.10
% 3.05/1.47  Demodulation         : 0.06
% 3.05/1.47  BG Simplification    : 0.02
% 3.05/1.47  Subsumption          : 0.06
% 3.05/1.47  Abstraction          : 0.02
% 3.05/1.47  MUC search           : 0.00
% 3.05/1.47  Cooper               : 0.00
% 3.05/1.47  Total                : 0.70
% 3.05/1.47  Index Insertion      : 0.00
% 3.05/1.47  Index Deletion       : 0.00
% 3.05/1.47  Index Matching       : 0.00
% 3.05/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
