%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 137 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 ( 237 expanded)
%              Number of equality atoms :   20 (  84 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_mcart_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_16,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_71,plain,(
    ! [C_35,B_36,A_37] :
      ( ~ v1_xboole_0(C_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_29,c_71])).

tff(c_77,plain,(
    ! [A_38] : ~ r2_hidden(A_38,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_12,plain,(
    ! [A_6] : k10_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_6] : k10_relat_1('#skF_4',A_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_12])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_29])).

tff(c_89,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_8])).

tff(c_159,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k8_relset_1(A_59,B_60,C_61,D_62) = k10_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [B_72,C_73,D_74] :
      ( k8_relset_1('#skF_4',B_72,C_73,D_74) = k10_relat_1(C_73,D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_159])).

tff(c_179,plain,(
    ! [B_72,D_74] : k8_relset_1('#skF_4',B_72,'#skF_4',D_74) = k10_relat_1('#skF_4',D_74) ),
    inference(resolution,[status(thm)],[c_88,c_177])).

tff(c_181,plain,(
    ! [B_72,D_74] : k8_relset_1('#skF_4',B_72,'#skF_4',D_74) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_179])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_22])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.57  
% 2.28/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.57  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_mcart_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.28/1.57  
% 2.28/1.57  %Foreground sorts:
% 2.28/1.57  
% 2.28/1.57  
% 2.28/1.57  %Background operators:
% 2.28/1.57  
% 2.28/1.57  
% 2.28/1.57  %Foreground operators:
% 2.28/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.57  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.28/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.57  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.28/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.57  
% 2.37/1.59  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.37/1.59  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.37/1.59  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.37/1.59  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.37/1.59  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.37/1.59  tff(f_41, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.37/1.59  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.37/1.59  tff(c_16, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.59  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.37/1.59  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.59  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.37/1.59  tff(c_29, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 2.37/1.59  tff(c_71, plain, (![C_35, B_36, A_37]: (~v1_xboole_0(C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.59  tff(c_73, plain, (![A_37]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_37, '#skF_4'))), inference(resolution, [status(thm)], [c_29, c_71])).
% 2.37/1.59  tff(c_77, plain, (![A_38]: (~r2_hidden(A_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_73])).
% 2.37/1.59  tff(c_82, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.37/1.59  tff(c_12, plain, (![A_6]: (k10_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.59  tff(c_86, plain, (![A_6]: (k10_relat_1('#skF_4', A_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_12])).
% 2.37/1.59  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_29])).
% 2.37/1.59  tff(c_89, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_8])).
% 2.37/1.59  tff(c_159, plain, (![A_59, B_60, C_61, D_62]: (k8_relset_1(A_59, B_60, C_61, D_62)=k10_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.37/1.59  tff(c_177, plain, (![B_72, C_73, D_74]: (k8_relset_1('#skF_4', B_72, C_73, D_74)=k10_relat_1(C_73, D_74) | ~m1_subset_1(C_73, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_159])).
% 2.37/1.59  tff(c_179, plain, (![B_72, D_74]: (k8_relset_1('#skF_4', B_72, '#skF_4', D_74)=k10_relat_1('#skF_4', D_74))), inference(resolution, [status(thm)], [c_88, c_177])).
% 2.37/1.59  tff(c_181, plain, (![B_72, D_74]: (k8_relset_1('#skF_4', B_72, '#skF_4', D_74)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_179])).
% 2.37/1.59  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.37/1.59  tff(c_84, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_22])).
% 2.37/1.59  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_84])).
% 2.37/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.59  
% 2.37/1.59  Inference rules
% 2.37/1.59  ----------------------
% 2.37/1.59  #Ref     : 0
% 2.37/1.59  #Sup     : 34
% 2.37/1.59  #Fact    : 0
% 2.37/1.59  #Define  : 0
% 2.37/1.59  #Split   : 0
% 2.37/1.59  #Chain   : 0
% 2.37/1.59  #Close   : 0
% 2.37/1.59  
% 2.37/1.59  Ordering : KBO
% 2.37/1.59  
% 2.37/1.59  Simplification rules
% 2.37/1.59  ----------------------
% 2.37/1.59  #Subsume      : 1
% 2.37/1.59  #Demod        : 23
% 2.37/1.59  #Tautology    : 25
% 2.37/1.59  #SimpNegUnit  : 0
% 2.37/1.59  #BackRed      : 10
% 2.37/1.59  
% 2.37/1.59  #Partial instantiations: 0
% 2.37/1.59  #Strategies tried      : 1
% 2.37/1.59  
% 2.37/1.59  Timing (in seconds)
% 2.37/1.59  ----------------------
% 2.37/1.59  Preprocessing        : 0.46
% 2.37/1.59  Parsing              : 0.23
% 2.37/1.59  CNF conversion       : 0.03
% 2.37/1.59  Main loop            : 0.24
% 2.37/1.59  Inferencing          : 0.08
% 2.37/1.59  Reduction            : 0.08
% 2.37/1.59  Demodulation         : 0.06
% 2.37/1.59  BG Simplification    : 0.02
% 2.37/1.60  Subsumption          : 0.04
% 2.37/1.60  Abstraction          : 0.02
% 2.37/1.60  MUC search           : 0.00
% 2.37/1.60  Cooper               : 0.00
% 2.37/1.60  Total                : 0.74
% 2.37/1.60  Index Insertion      : 0.00
% 2.37/1.60  Index Deletion       : 0.00
% 2.37/1.60  Index Matching       : 0.00
% 2.37/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
