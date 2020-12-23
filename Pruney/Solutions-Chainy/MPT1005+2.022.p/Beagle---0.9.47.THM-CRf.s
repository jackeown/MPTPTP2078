%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:02 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 136 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 ( 216 expanded)
%              Number of equality atoms :   19 (  77 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_25,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_67,plain,(
    ! [C_19,B_20,A_21] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_21,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_25,c_67])).

tff(c_73,plain,(
    ! [A_22] : ~ r2_hidden(A_22,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_78,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_14,plain,(
    ! [A_8] : k9_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_8] : k9_relat_1('#skF_4',A_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_14])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_25])).

tff(c_82,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_10])).

tff(c_99,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( k7_relset_1(A_24,B_25,C_26,D_27) = k9_relat_1(C_26,D_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_161,plain,(
    ! [B_38,C_39,D_40] :
      ( k7_relset_1('#skF_4',B_38,C_39,D_40) = k9_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_99])).

tff(c_163,plain,(
    ! [B_38,D_40] : k7_relset_1('#skF_4',B_38,'#skF_4',D_40) = k9_relat_1('#skF_4',D_40) ),
    inference(resolution,[status(thm)],[c_85,c_161])).

tff(c_165,plain,(
    ! [B_38,D_40] : k7_relset_1('#skF_4',B_38,'#skF_4',D_40) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_163])).

tff(c_18,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_18])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.16  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.66/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.16  
% 1.66/1.17  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.66/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.66/1.17  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.66/1.17  tff(f_62, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 1.66/1.17  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.66/1.17  tff(f_49, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.66/1.17  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.66/1.17  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.66/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.66/1.17  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.17  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.66/1.17  tff(c_25, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.66/1.17  tff(c_67, plain, (![C_19, B_20, A_21]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_20, k1_zfmisc_1(C_19)) | ~r2_hidden(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.17  tff(c_69, plain, (![A_21]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_21, '#skF_4'))), inference(resolution, [status(thm)], [c_25, c_67])).
% 1.66/1.17  tff(c_73, plain, (![A_22]: (~r2_hidden(A_22, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_69])).
% 1.66/1.17  tff(c_78, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_73])).
% 1.66/1.17  tff(c_14, plain, (![A_8]: (k9_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.66/1.17  tff(c_83, plain, (![A_8]: (k9_relat_1('#skF_4', A_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_14])).
% 1.66/1.17  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_25])).
% 1.66/1.17  tff(c_82, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_10])).
% 1.66/1.17  tff(c_99, plain, (![A_24, B_25, C_26, D_27]: (k7_relset_1(A_24, B_25, C_26, D_27)=k9_relat_1(C_26, D_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.17  tff(c_161, plain, (![B_38, C_39, D_40]: (k7_relset_1('#skF_4', B_38, C_39, D_40)=k9_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_99])).
% 1.66/1.17  tff(c_163, plain, (![B_38, D_40]: (k7_relset_1('#skF_4', B_38, '#skF_4', D_40)=k9_relat_1('#skF_4', D_40))), inference(resolution, [status(thm)], [c_85, c_161])).
% 1.66/1.17  tff(c_165, plain, (![B_38, D_40]: (k7_relset_1('#skF_4', B_38, '#skF_4', D_40)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_163])).
% 1.66/1.17  tff(c_18, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.66/1.17  tff(c_81, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_18])).
% 1.66/1.17  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_81])).
% 1.66/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  Inference rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Ref     : 0
% 1.66/1.17  #Sup     : 32
% 1.66/1.17  #Fact    : 0
% 1.66/1.17  #Define  : 0
% 1.66/1.17  #Split   : 0
% 1.66/1.17  #Chain   : 0
% 1.66/1.17  #Close   : 0
% 1.66/1.17  
% 1.66/1.17  Ordering : KBO
% 1.66/1.17  
% 1.66/1.17  Simplification rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Subsume      : 1
% 1.66/1.17  #Demod        : 21
% 1.66/1.17  #Tautology    : 25
% 1.66/1.17  #SimpNegUnit  : 0
% 1.66/1.17  #BackRed      : 10
% 1.66/1.17  
% 1.66/1.17  #Partial instantiations: 0
% 1.66/1.17  #Strategies tried      : 1
% 1.66/1.17  
% 1.66/1.17  Timing (in seconds)
% 1.66/1.17  ----------------------
% 1.66/1.17  Preprocessing        : 0.29
% 1.66/1.17  Parsing              : 0.15
% 1.66/1.17  CNF conversion       : 0.02
% 1.66/1.17  Main loop            : 0.13
% 1.66/1.17  Inferencing          : 0.05
% 1.66/1.17  Reduction            : 0.04
% 1.66/1.17  Demodulation         : 0.03
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.02
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.44
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.66/1.17  Index Matching       : 0.00
% 1.66/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
