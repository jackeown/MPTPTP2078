%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_20,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k2_relset_1(A_30,B_31,C_32),k1_zfmisc_1(B_31))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k2_relset_1(A_40,B_41,C_42),B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(resolution,[status(thm)],[c_63,c_8])).

tff(c_93,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_78,plain,(
    ! [D_36,C_37,A_38,B_39] :
      ( r2_hidden(k1_funct_1(D_36,C_37),k2_relset_1(A_38,B_39,D_36))
      | k1_xboole_0 = B_39
      | ~ r2_hidden(C_37,A_38)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(D_36,A_38,B_39)
      | ~ v1_funct_1(D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_46,B_50,C_49,D_47,B_48] :
      ( r2_hidden(k1_funct_1(D_47,C_49),B_50)
      | ~ r1_tarski(k2_relset_1(A_46,B_48,D_47),B_50)
      | k1_xboole_0 = B_48
      | ~ r2_hidden(C_49,A_46)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_46,B_48)))
      | ~ v1_funct_2(D_47,A_46,B_48)
      | ~ v1_funct_1(D_47) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_106,plain,(
    ! [C_49] :
      ( r2_hidden(k1_funct_1('#skF_5',C_49),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_49,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_93,c_102])).

tff(c_113,plain,(
    ! [C_49] :
      ( r2_hidden(k1_funct_1('#skF_5',C_49),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_49,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_106])).

tff(c_116,plain,(
    ! [C_51] :
      ( r2_hidden(k1_funct_1('#skF_5',C_51),'#skF_3')
      | ~ r2_hidden(C_51,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_113])).

tff(c_16,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_121,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_16])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.89/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.19  
% 1.89/1.20  tff(f_65, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.89/1.20  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 1.89/1.20  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.89/1.20  tff(f_52, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 1.89/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.89/1.20  tff(c_20, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_24, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_63, plain, (![A_30, B_31, C_32]: (m1_subset_1(k2_relset_1(A_30, B_31, C_32), k1_zfmisc_1(B_31)) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.20  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.89/1.20  tff(c_82, plain, (![A_40, B_41, C_42]: (r1_tarski(k2_relset_1(A_40, B_41, C_42), B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(resolution, [status(thm)], [c_63, c_8])).
% 1.89/1.20  tff(c_93, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_22, c_82])).
% 1.89/1.20  tff(c_78, plain, (![D_36, C_37, A_38, B_39]: (r2_hidden(k1_funct_1(D_36, C_37), k2_relset_1(A_38, B_39, D_36)) | k1_xboole_0=B_39 | ~r2_hidden(C_37, A_38) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(D_36, A_38, B_39) | ~v1_funct_1(D_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.20  tff(c_102, plain, (![A_46, B_50, C_49, D_47, B_48]: (r2_hidden(k1_funct_1(D_47, C_49), B_50) | ~r1_tarski(k2_relset_1(A_46, B_48, D_47), B_50) | k1_xboole_0=B_48 | ~r2_hidden(C_49, A_46) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_46, B_48))) | ~v1_funct_2(D_47, A_46, B_48) | ~v1_funct_1(D_47))), inference(resolution, [status(thm)], [c_78, c_2])).
% 1.89/1.20  tff(c_106, plain, (![C_49]: (r2_hidden(k1_funct_1('#skF_5', C_49), '#skF_3') | k1_xboole_0='#skF_3' | ~r2_hidden(C_49, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_93, c_102])).
% 1.89/1.20  tff(c_113, plain, (![C_49]: (r2_hidden(k1_funct_1('#skF_5', C_49), '#skF_3') | k1_xboole_0='#skF_3' | ~r2_hidden(C_49, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_106])).
% 1.89/1.20  tff(c_116, plain, (![C_51]: (r2_hidden(k1_funct_1('#skF_5', C_51), '#skF_3') | ~r2_hidden(C_51, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_113])).
% 1.89/1.20  tff(c_16, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.20  tff(c_121, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_116, c_16])).
% 1.89/1.20  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_121])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 22
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 2
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 2
% 1.89/1.20  #Demod        : 4
% 1.89/1.20  #Tautology    : 2
% 1.89/1.20  #SimpNegUnit  : 1
% 1.89/1.20  #BackRed      : 0
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.20  Preprocessing        : 0.28
% 1.89/1.20  Parsing              : 0.15
% 1.89/1.20  CNF conversion       : 0.02
% 1.89/1.20  Main loop            : 0.16
% 1.89/1.20  Inferencing          : 0.06
% 1.89/1.20  Reduction            : 0.04
% 1.89/1.20  Demodulation         : 0.03
% 1.89/1.20  BG Simplification    : 0.01
% 1.89/1.20  Subsumption          : 0.04
% 1.89/1.20  Abstraction          : 0.01
% 1.98/1.20  MUC search           : 0.00
% 1.98/1.20  Cooper               : 0.00
% 1.98/1.20  Total                : 0.46
% 1.98/1.20  Index Insertion      : 0.00
% 1.98/1.20  Index Deletion       : 0.00
% 1.98/1.20  Index Matching       : 0.00
% 1.98/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
