%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:02 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 137 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 ( 258 expanded)
%              Number of equality atoms :   19 (  77 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_66,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22])).

tff(c_69,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_41,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_27,c_69])).

tff(c_75,plain,(
    ! [A_42] : ~ r2_hidden(A_42,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_71])).

tff(c_80,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_12,plain,(
    ! [A_6] : k9_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [A_6] : k9_relat_1('#skF_4',A_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_12])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_27])).

tff(c_111,plain,(
    ! [B_49] : k2_zfmisc_1('#skF_4',B_49) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_8])).

tff(c_14,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( k7_relset_1(A_7,B_8,C_9,D_10) = k9_relat_1(C_9,D_10)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_53,C_54,D_55] :
      ( k7_relset_1('#skF_4',B_53,C_54,D_55) = k9_relat_1(C_54,D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_14])).

tff(c_153,plain,(
    ! [B_53,D_55] : k7_relset_1('#skF_4',B_53,'#skF_4',D_55) = k9_relat_1('#skF_4',D_55) ),
    inference(resolution,[status(thm)],[c_85,c_151])).

tff(c_155,plain,(
    ! [B_53,D_55] : k7_relset_1('#skF_4',B_53,'#skF_4',D_55) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_153])).

tff(c_20,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_82,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_20])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:34:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.32  
% 1.87/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.08/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.33  
% 2.08/1.34  tff(f_66, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.08/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.08/1.34  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.08/1.34  tff(f_75, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 2.08/1.34  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.08/1.34  tff(f_41, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.08/1.34  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.08/1.34  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.08/1.34  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.34  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.08/1.34  tff(c_27, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22])).
% 2.08/1.34  tff(c_69, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.34  tff(c_71, plain, (![A_41]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_41, '#skF_4'))), inference(resolution, [status(thm)], [c_27, c_69])).
% 2.08/1.34  tff(c_75, plain, (![A_42]: (~r2_hidden(A_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_71])).
% 2.08/1.34  tff(c_80, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_75])).
% 2.08/1.34  tff(c_12, plain, (![A_6]: (k9_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.34  tff(c_84, plain, (![A_6]: (k9_relat_1('#skF_4', A_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_12])).
% 2.08/1.34  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_27])).
% 2.08/1.34  tff(c_111, plain, (![B_49]: (k2_zfmisc_1('#skF_4', B_49)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_8])).
% 2.08/1.34  tff(c_14, plain, (![A_7, B_8, C_9, D_10]: (k7_relset_1(A_7, B_8, C_9, D_10)=k9_relat_1(C_9, D_10) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.34  tff(c_151, plain, (![B_53, C_54, D_55]: (k7_relset_1('#skF_4', B_53, C_54, D_55)=k9_relat_1(C_54, D_55) | ~m1_subset_1(C_54, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_14])).
% 2.08/1.34  tff(c_153, plain, (![B_53, D_55]: (k7_relset_1('#skF_4', B_53, '#skF_4', D_55)=k9_relat_1('#skF_4', D_55))), inference(resolution, [status(thm)], [c_85, c_151])).
% 2.08/1.34  tff(c_155, plain, (![B_53, D_55]: (k7_relset_1('#skF_4', B_53, '#skF_4', D_55)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_153])).
% 2.08/1.34  tff(c_20, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.08/1.34  tff(c_82, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_20])).
% 2.08/1.34  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_82])).
% 2.08/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.34  
% 2.08/1.34  Inference rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Ref     : 0
% 2.08/1.34  #Sup     : 29
% 2.08/1.34  #Fact    : 0
% 2.08/1.34  #Define  : 0
% 2.08/1.34  #Split   : 0
% 2.08/1.34  #Chain   : 0
% 2.08/1.34  #Close   : 0
% 2.08/1.34  
% 2.08/1.34  Ordering : KBO
% 2.08/1.34  
% 2.08/1.34  Simplification rules
% 2.08/1.34  ----------------------
% 2.08/1.34  #Subsume      : 1
% 2.08/1.34  #Demod        : 20
% 2.08/1.34  #Tautology    : 23
% 2.08/1.34  #SimpNegUnit  : 0
% 2.08/1.34  #BackRed      : 10
% 2.08/1.34  
% 2.08/1.34  #Partial instantiations: 0
% 2.08/1.34  #Strategies tried      : 1
% 2.08/1.34  
% 2.08/1.34  Timing (in seconds)
% 2.08/1.34  ----------------------
% 2.08/1.34  Preprocessing        : 0.37
% 2.08/1.34  Parsing              : 0.21
% 2.08/1.34  CNF conversion       : 0.02
% 2.08/1.34  Main loop            : 0.14
% 2.08/1.34  Inferencing          : 0.05
% 2.08/1.34  Reduction            : 0.05
% 2.08/1.34  Demodulation         : 0.04
% 2.08/1.34  BG Simplification    : 0.01
% 2.08/1.34  Subsumption          : 0.02
% 2.08/1.34  Abstraction          : 0.01
% 2.08/1.34  MUC search           : 0.00
% 2.08/1.34  Cooper               : 0.00
% 2.08/1.34  Total                : 0.54
% 2.08/1.34  Index Insertion      : 0.00
% 2.08/1.34  Index Deletion       : 0.00
% 2.08/1.34  Index Matching       : 0.00
% 2.08/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
