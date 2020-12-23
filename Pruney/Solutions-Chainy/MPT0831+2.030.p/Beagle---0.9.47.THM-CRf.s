%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:36 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  89 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( r2_relset_1(A_46,B_47,C_48,C_48)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    ! [C_50] :
      ( r2_relset_1('#skF_2','#skF_1',C_50,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_92,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_35])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [E_55,D_52,C_53,A_51,B_54] :
      ( m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(B_54,D_52)))
      | ~ r1_tarski(C_53,D_52)
      | ~ r1_tarski(A_51,B_54)
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(A_51,C_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_100,plain,(
    ! [E_56,B_57,B_58,A_59] :
      ( m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(B_57,B_58)))
      | ~ r1_tarski(A_59,B_57)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_107,plain,(
    ! [E_60,B_61] :
      ( m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_61)))
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_61))) ) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_111,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_16,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_16])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_142,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_12])).

tff(c_145,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_142])).

tff(c_71,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k5_relset_1(A_41,B_42,C_43,D_44) = k7_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ! [D_44] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_44) = k7_relat_1('#skF_4',D_44) ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_75,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_146,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_75])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.98/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.98/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.19  
% 2.07/1.21  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.07/1.21  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.07/1.21  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.07/1.21  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.07/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.07/1.21  tff(f_70, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 2.07/1.21  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.07/1.21  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.07/1.21  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.07/1.21  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.21  tff(c_85, plain, (![A_46, B_47, C_48, D_49]: (r2_relset_1(A_46, B_47, C_48, C_48) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.21  tff(c_89, plain, (![C_50]: (r2_relset_1('#skF_2', '#skF_1', C_50, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_28, c_85])).
% 2.07/1.21  tff(c_92, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_89])).
% 2.07/1.21  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.21  tff(c_32, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.07/1.21  tff(c_35, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.07/1.21  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_35])).
% 2.07/1.21  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.21  tff(c_93, plain, (![E_55, D_52, C_53, A_51, B_54]: (m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(B_54, D_52))) | ~r1_tarski(C_53, D_52) | ~r1_tarski(A_51, B_54) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(A_51, C_53))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.07/1.21  tff(c_100, plain, (![E_56, B_57, B_58, A_59]: (m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(B_57, B_58))) | ~r1_tarski(A_59, B_57) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.07/1.21  tff(c_107, plain, (![E_60, B_61]: (m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_61))) | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_61))))), inference(resolution, [status(thm)], [c_26, c_100])).
% 2.07/1.21  tff(c_111, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_107])).
% 2.07/1.21  tff(c_16, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.21  tff(c_136, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_111, c_16])).
% 2.07/1.21  tff(c_12, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.21  tff(c_142, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_12])).
% 2.07/1.21  tff(c_145, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_142])).
% 2.07/1.21  tff(c_71, plain, (![A_41, B_42, C_43, D_44]: (k5_relset_1(A_41, B_42, C_43, D_44)=k7_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.21  tff(c_74, plain, (![D_44]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44))), inference(resolution, [status(thm)], [c_28, c_71])).
% 2.07/1.21  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.21  tff(c_75, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_24])).
% 2.07/1.21  tff(c_146, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_75])).
% 2.07/1.21  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_146])).
% 2.07/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  Inference rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Ref     : 0
% 2.07/1.21  #Sup     : 26
% 2.07/1.21  #Fact    : 0
% 2.07/1.21  #Define  : 0
% 2.07/1.21  #Split   : 1
% 2.07/1.21  #Chain   : 0
% 2.07/1.21  #Close   : 0
% 2.07/1.21  
% 2.07/1.21  Ordering : KBO
% 2.07/1.21  
% 2.07/1.21  Simplification rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Subsume      : 0
% 2.07/1.21  #Demod        : 11
% 2.07/1.21  #Tautology    : 9
% 2.07/1.21  #SimpNegUnit  : 0
% 2.07/1.21  #BackRed      : 2
% 2.07/1.21  
% 2.07/1.21  #Partial instantiations: 0
% 2.07/1.21  #Strategies tried      : 1
% 2.07/1.21  
% 2.07/1.21  Timing (in seconds)
% 2.07/1.21  ----------------------
% 2.07/1.21  Preprocessing        : 0.30
% 2.07/1.21  Parsing              : 0.16
% 2.07/1.21  CNF conversion       : 0.02
% 2.07/1.21  Main loop            : 0.15
% 2.07/1.21  Inferencing          : 0.05
% 2.07/1.21  Reduction            : 0.05
% 2.07/1.21  Demodulation         : 0.04
% 2.07/1.21  BG Simplification    : 0.01
% 2.07/1.21  Subsumption          : 0.02
% 2.07/1.21  Abstraction          : 0.01
% 2.07/1.21  MUC search           : 0.00
% 2.07/1.21  Cooper               : 0.00
% 2.07/1.21  Total                : 0.48
% 2.07/1.21  Index Insertion      : 0.00
% 2.07/1.21  Index Deletion       : 0.00
% 2.07/1.21  Index Matching       : 0.00
% 2.07/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
