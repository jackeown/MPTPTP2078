%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:52 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( m1_subset_1(k7_relset_1(A_30,B_31,C_32,D_33),k1_zfmisc_1(B_31))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_18,A_1] :
      ( r1_tarski(A_18,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_18,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_41,plain,(
    ! [A_18,A_1] :
      ( r1_tarski(A_18,A_1)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_38])).

tff(c_75,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( r1_tarski(k7_relset_1(A_36,B_37,C_38,D_39),B_37)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(resolution,[status(thm)],[c_69,c_41])).

tff(c_82,plain,(
    ! [D_39] : r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_6',D_39),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_20,plain,(
    ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.65/1.13  
% 1.65/1.13  %Foreground sorts:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Background operators:
% 1.65/1.13  
% 1.65/1.13  
% 1.65/1.13  %Foreground operators:
% 1.65/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.13  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.65/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.65/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.65/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.65/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.13  
% 1.65/1.14  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 1.65/1.14  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 1.65/1.14  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.65/1.14  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.65/1.14  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.65/1.14  tff(c_22, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.65/1.14  tff(c_69, plain, (![A_30, B_31, C_32, D_33]: (m1_subset_1(k7_relset_1(A_30, B_31, C_32, D_33), k1_zfmisc_1(B_31)) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.14  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.14  tff(c_34, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.14  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.14  tff(c_38, plain, (![A_18, A_1]: (r1_tarski(A_18, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_18, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.65/1.14  tff(c_41, plain, (![A_18, A_1]: (r1_tarski(A_18, A_1) | ~m1_subset_1(A_18, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_38])).
% 1.65/1.14  tff(c_75, plain, (![A_36, B_37, C_38, D_39]: (r1_tarski(k7_relset_1(A_36, B_37, C_38, D_39), B_37) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(resolution, [status(thm)], [c_69, c_41])).
% 1.65/1.14  tff(c_82, plain, (![D_39]: (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_39), '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_75])).
% 1.65/1.14  tff(c_20, plain, (~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.65/1.14  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_20])).
% 1.65/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.14  
% 1.65/1.14  Inference rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Ref     : 0
% 1.65/1.14  #Sup     : 10
% 1.65/1.14  #Fact    : 0
% 1.65/1.14  #Define  : 0
% 1.65/1.14  #Split   : 0
% 1.65/1.14  #Chain   : 0
% 1.65/1.14  #Close   : 0
% 1.65/1.14  
% 1.65/1.14  Ordering : KBO
% 1.65/1.14  
% 1.65/1.14  Simplification rules
% 1.65/1.14  ----------------------
% 1.65/1.14  #Subsume      : 0
% 1.65/1.14  #Demod        : 1
% 1.65/1.14  #Tautology    : 1
% 1.65/1.14  #SimpNegUnit  : 1
% 1.65/1.14  #BackRed      : 1
% 1.65/1.14  
% 1.65/1.14  #Partial instantiations: 0
% 1.65/1.14  #Strategies tried      : 1
% 1.65/1.14  
% 1.65/1.14  Timing (in seconds)
% 1.65/1.14  ----------------------
% 1.65/1.15  Preprocessing        : 0.28
% 1.65/1.15  Parsing              : 0.15
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.12
% 1.65/1.15  Inferencing          : 0.05
% 1.65/1.15  Reduction            : 0.03
% 1.65/1.15  Demodulation         : 0.02
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.02
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.42
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
