%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:00 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 103 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 ( 172 expanded)
%              Number of equality atoms :   15 (  41 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k3_mcart_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_45,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_xboole_0(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_51,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_48])).

tff(c_40,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32),A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_40,c_2])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_51,c_52])).

tff(c_8,plain,(
    ! [A_5] : k9_relat_1(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    ! [A_5] : k9_relat_1('#skF_5',A_5) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_8])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_22])).

tff(c_118,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k7_relset_1(A_60,B_61,C_62,D_63) = k9_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [D_63] : k7_relset_1('#skF_5','#skF_3','#skF_5',D_63) = k9_relat_1('#skF_5',D_63) ),
    inference(resolution,[status(thm)],[c_64,c_118])).

tff(c_122,plain,(
    ! [D_63] : k7_relset_1('#skF_5','#skF_3','#skF_5',D_63) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_120])).

tff(c_20,plain,(
    k7_relset_1(k1_xboole_0,'#skF_3','#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    k7_relset_1('#skF_5','#skF_3','#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_20])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:16:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k3_mcart_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 1.80/1.17  
% 1.80/1.17  %Foreground sorts:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Background operators:
% 1.80/1.17  
% 1.80/1.17  
% 1.80/1.17  %Foreground operators:
% 1.80/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.80/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.17  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.80/1.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.80/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.80/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.80/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.17  
% 1.90/1.18  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.18  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.90/1.18  tff(f_41, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 1.90/1.18  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 1.90/1.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.90/1.18  tff(f_34, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.90/1.18  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.90/1.18  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.18  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.90/1.18  tff(c_45, plain, (![C_33, A_34, B_35]: (v1_xboole_0(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.18  tff(c_48, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_45])).
% 1.90/1.18  tff(c_51, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_48])).
% 1.90/1.18  tff(c_40, plain, (![A_32]: (r2_hidden('#skF_2'(A_32), A_32) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.18  tff(c_52, plain, (![A_36]: (~v1_xboole_0(A_36) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_40, c_2])).
% 1.90/1.18  tff(c_59, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_51, c_52])).
% 1.90/1.18  tff(c_8, plain, (![A_5]: (k9_relat_1(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.18  tff(c_66, plain, (![A_5]: (k9_relat_1('#skF_5', A_5)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_8])).
% 1.90/1.18  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_22])).
% 1.90/1.18  tff(c_118, plain, (![A_60, B_61, C_62, D_63]: (k7_relset_1(A_60, B_61, C_62, D_63)=k9_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.18  tff(c_120, plain, (![D_63]: (k7_relset_1('#skF_5', '#skF_3', '#skF_5', D_63)=k9_relat_1('#skF_5', D_63))), inference(resolution, [status(thm)], [c_64, c_118])).
% 1.90/1.18  tff(c_122, plain, (![D_63]: (k7_relset_1('#skF_5', '#skF_3', '#skF_5', D_63)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_120])).
% 1.90/1.18  tff(c_20, plain, (k7_relset_1(k1_xboole_0, '#skF_3', '#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.90/1.18  tff(c_65, plain, (k7_relset_1('#skF_5', '#skF_3', '#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_20])).
% 1.90/1.18  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_65])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 19
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 1
% 1.90/1.18  #Demod        : 17
% 1.90/1.18  #Tautology    : 11
% 1.90/1.18  #SimpNegUnit  : 0
% 1.90/1.18  #BackRed      : 8
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.19  Preprocessing        : 0.30
% 1.90/1.19  Parsing              : 0.16
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.13
% 1.90/1.19  Inferencing          : 0.05
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
