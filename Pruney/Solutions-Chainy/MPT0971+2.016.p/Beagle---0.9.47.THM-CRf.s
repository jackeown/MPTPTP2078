%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:31 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 163 expanded)
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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_4'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [A_92,C_93] :
      ( r2_hidden(k4_tarski(A_92,k1_funct_1(C_93,A_92)),C_93)
      | ~ r2_hidden(A_92,k1_relat_1(C_93))
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ! [A_114,C_115,A_116] :
      ( r2_hidden(k4_tarski(A_114,k1_funct_1(C_115,A_114)),A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_116))
      | ~ r2_hidden(A_114,k1_relat_1(C_115))
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_117,C_118,C_119,D_120] :
      ( r2_hidden(A_117,C_118)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(C_118,D_120)))
      | ~ r2_hidden(A_117,k1_relat_1(C_119))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_196,c_6])).

tff(c_233,plain,(
    ! [A_117] :
      ( r2_hidden(A_117,'#skF_5')
      | ~ r2_hidden(A_117,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_231])).

tff(c_237,plain,(
    ! [A_121] :
      ( r2_hidden(A_121,'#skF_5')
      | ~ r2_hidden(A_121,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_233])).

tff(c_257,plain,(
    ! [C_45] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_45),'#skF_5')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_237])).

tff(c_272,plain,(
    ! [C_122] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_122),'#skF_5')
      | ~ r2_hidden(C_122,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_257])).

tff(c_38,plain,(
    ! [E_59] :
      ( k1_funct_1('#skF_8',E_59) != '#skF_7'
      | ~ r2_hidden(E_59,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_316,plain,(
    ! [C_125] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_125)) != '#skF_7'
      | ~ r2_hidden(C_125,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_272,c_38])).

tff(c_320,plain,(
    ! [C_45] :
      ( C_45 != '#skF_7'
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_316])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_320])).

tff(c_60,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_40,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.35  
% 2.34/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.34/1.35  
% 2.34/1.35  %Foreground sorts:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Background operators:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Foreground operators:
% 2.34/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.34/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.34/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.34/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.34/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.35  
% 2.34/1.37  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.34/1.37  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.34/1.37  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.34/1.37  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.34/1.37  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.34/1.37  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 2.34/1.37  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.34/1.37  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.34/1.37  tff(c_48, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.34/1.37  tff(c_52, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_48])).
% 2.34/1.37  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.34/1.37  tff(c_12, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_4'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.34/1.37  tff(c_14, plain, (![A_9, C_45]: (r2_hidden('#skF_4'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.34/1.37  tff(c_101, plain, (![A_92, C_93]: (r2_hidden(k4_tarski(A_92, k1_funct_1(C_93, A_92)), C_93) | ~r2_hidden(A_92, k1_relat_1(C_93)) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.34/1.37  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.37  tff(c_196, plain, (![A_114, C_115, A_116]: (r2_hidden(k4_tarski(A_114, k1_funct_1(C_115, A_114)), A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(A_116)) | ~r2_hidden(A_114, k1_relat_1(C_115)) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_101, c_8])).
% 2.34/1.37  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.37  tff(c_231, plain, (![A_117, C_118, C_119, D_120]: (r2_hidden(A_117, C_118) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(C_118, D_120))) | ~r2_hidden(A_117, k1_relat_1(C_119)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_196, c_6])).
% 2.34/1.37  tff(c_233, plain, (![A_117]: (r2_hidden(A_117, '#skF_5') | ~r2_hidden(A_117, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_231])).
% 2.34/1.37  tff(c_237, plain, (![A_121]: (r2_hidden(A_121, '#skF_5') | ~r2_hidden(A_121, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_233])).
% 2.34/1.37  tff(c_257, plain, (![C_45]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_45), '#skF_5') | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_14, c_237])).
% 2.34/1.37  tff(c_272, plain, (![C_122]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_122), '#skF_5') | ~r2_hidden(C_122, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_257])).
% 2.34/1.37  tff(c_38, plain, (![E_59]: (k1_funct_1('#skF_8', E_59)!='#skF_7' | ~r2_hidden(E_59, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.34/1.37  tff(c_316, plain, (![C_125]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_125))!='#skF_7' | ~r2_hidden(C_125, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_272, c_38])).
% 2.34/1.37  tff(c_320, plain, (![C_45]: (C_45!='#skF_7' | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_316])).
% 2.34/1.37  tff(c_323, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_320])).
% 2.34/1.37  tff(c_60, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.37  tff(c_64, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_60])).
% 2.34/1.37  tff(c_40, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.34/1.37  tff(c_66, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 2.34/1.37  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_66])).
% 2.34/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.37  
% 2.34/1.37  Inference rules
% 2.34/1.37  ----------------------
% 2.34/1.37  #Ref     : 0
% 2.34/1.37  #Sup     : 59
% 2.34/1.37  #Fact    : 0
% 2.34/1.37  #Define  : 0
% 2.34/1.37  #Split   : 1
% 2.34/1.37  #Chain   : 0
% 2.34/1.37  #Close   : 0
% 2.34/1.37  
% 2.34/1.37  Ordering : KBO
% 2.34/1.37  
% 2.34/1.37  Simplification rules
% 2.34/1.37  ----------------------
% 2.34/1.37  #Subsume      : 1
% 2.34/1.37  #Demod        : 10
% 2.34/1.37  #Tautology    : 11
% 2.34/1.37  #SimpNegUnit  : 1
% 2.34/1.37  #BackRed      : 3
% 2.34/1.37  
% 2.34/1.37  #Partial instantiations: 0
% 2.34/1.37  #Strategies tried      : 1
% 2.34/1.37  
% 2.34/1.37  Timing (in seconds)
% 2.34/1.37  ----------------------
% 2.34/1.37  Preprocessing        : 0.31
% 2.34/1.37  Parsing              : 0.16
% 2.34/1.37  CNF conversion       : 0.03
% 2.34/1.37  Main loop            : 0.28
% 2.34/1.37  Inferencing          : 0.11
% 2.34/1.37  Reduction            : 0.07
% 2.34/1.37  Demodulation         : 0.05
% 2.34/1.37  BG Simplification    : 0.02
% 2.34/1.37  Subsumption          : 0.06
% 2.34/1.37  Abstraction          : 0.02
% 2.34/1.37  MUC search           : 0.00
% 2.34/1.37  Cooper               : 0.00
% 2.34/1.37  Total                : 0.63
% 2.34/1.37  Index Insertion      : 0.00
% 2.34/1.37  Index Deletion       : 0.00
% 2.34/1.37  Index Matching       : 0.00
% 2.34/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
