%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 102 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 ( 157 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_47])).

tff(c_53,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_31,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_2'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(resolution,[status(thm)],[c_31,c_2])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53,c_35])).

tff(c_10,plain,(
    ! [A_7] : k9_relat_1(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_7] : k9_relat_1('#skF_5',A_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_10])).

tff(c_61,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_18])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k7_relset_1(A_12,B_13,C_14,D_15) = k9_relat_1(C_14,D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    ! [D_15] : k7_relset_1('#skF_5','#skF_3','#skF_5',D_15) = k9_relat_1('#skF_5',D_15) ),
    inference(resolution,[status(thm)],[c_61,c_14])).

tff(c_90,plain,(
    ! [D_15] : k7_relset_1('#skF_5','#skF_3','#skF_5',D_15) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_85])).

tff(c_16,plain,(
    k7_relset_1(k1_xboole_0,'#skF_3','#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    k7_relset_1('#skF_5','#skF_3','#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_16])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 1.59/1.11  
% 1.59/1.11  %Foreground sorts:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Background operators:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Foreground operators:
% 1.59/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.59/1.11  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.59/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.11  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.59/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.59/1.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.59/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.59/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.59/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.59/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.59/1.11  
% 1.59/1.12  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.59/1.12  tff(f_62, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.59/1.12  tff(f_49, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 1.59/1.12  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.59/1.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.59/1.12  tff(f_42, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.59/1.12  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.59/1.12  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.59/1.12  tff(c_18, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.59/1.12  tff(c_47, plain, (![C_22, A_23, B_24]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.59/1.12  tff(c_50, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_47])).
% 1.59/1.12  tff(c_53, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50])).
% 1.59/1.12  tff(c_31, plain, (![A_19]: (r2_hidden('#skF_2'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.12  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.12  tff(c_35, plain, (![A_19]: (~v1_xboole_0(A_19) | k1_xboole_0=A_19)), inference(resolution, [status(thm)], [c_31, c_2])).
% 1.59/1.12  tff(c_57, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_53, c_35])).
% 1.59/1.12  tff(c_10, plain, (![A_7]: (k9_relat_1(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.12  tff(c_62, plain, (![A_7]: (k9_relat_1('#skF_5', A_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_10])).
% 1.59/1.12  tff(c_61, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_18])).
% 1.59/1.12  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k7_relset_1(A_12, B_13, C_14, D_15)=k9_relat_1(C_14, D_15) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.59/1.12  tff(c_85, plain, (![D_15]: (k7_relset_1('#skF_5', '#skF_3', '#skF_5', D_15)=k9_relat_1('#skF_5', D_15))), inference(resolution, [status(thm)], [c_61, c_14])).
% 1.59/1.12  tff(c_90, plain, (![D_15]: (k7_relset_1('#skF_5', '#skF_3', '#skF_5', D_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_85])).
% 1.59/1.12  tff(c_16, plain, (k7_relset_1(k1_xboole_0, '#skF_3', '#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.59/1.12  tff(c_60, plain, (k7_relset_1('#skF_5', '#skF_3', '#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_16])).
% 1.59/1.12  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_60])).
% 1.59/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  Inference rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Ref     : 0
% 1.59/1.12  #Sup     : 14
% 1.59/1.12  #Fact    : 0
% 1.59/1.12  #Define  : 0
% 1.59/1.12  #Split   : 0
% 1.59/1.12  #Chain   : 0
% 1.59/1.12  #Close   : 0
% 1.59/1.12  
% 1.59/1.12  Ordering : KBO
% 1.59/1.12  
% 1.59/1.12  Simplification rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Subsume      : 0
% 1.59/1.12  #Demod        : 15
% 1.59/1.12  #Tautology    : 11
% 1.59/1.12  #SimpNegUnit  : 0
% 1.59/1.12  #BackRed      : 8
% 1.59/1.12  
% 1.59/1.12  #Partial instantiations: 0
% 1.59/1.12  #Strategies tried      : 1
% 1.59/1.12  
% 1.59/1.12  Timing (in seconds)
% 1.59/1.12  ----------------------
% 1.59/1.12  Preprocessing        : 0.28
% 1.59/1.12  Parsing              : 0.15
% 1.59/1.12  CNF conversion       : 0.02
% 1.59/1.12  Main loop            : 0.10
% 1.59/1.12  Inferencing          : 0.04
% 1.59/1.12  Reduction            : 0.03
% 1.59/1.13  Demodulation         : 0.02
% 1.59/1.13  BG Simplification    : 0.01
% 1.59/1.13  Subsumption          : 0.01
% 1.59/1.13  Abstraction          : 0.01
% 1.59/1.13  MUC search           : 0.00
% 1.59/1.13  Cooper               : 0.00
% 1.59/1.13  Total                : 0.40
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
