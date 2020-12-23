%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:02 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
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
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k4_mcart_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,negated_conjecture,(
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
    ! [A_6] : k9_relat_1(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_6] : k9_relat_1('#skF_4',A_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_12])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_29])).

tff(c_89,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_8])).

tff(c_159,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k7_relset_1(A_59,B_60,C_61,D_62) = k9_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [B_72,C_73,D_74] :
      ( k7_relset_1('#skF_4',B_72,C_73,D_74) = k9_relat_1(C_73,D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_159])).

tff(c_179,plain,(
    ! [B_72,D_74] : k7_relset_1('#skF_4',B_72,'#skF_4',D_74) = k9_relat_1('#skF_4',D_74) ),
    inference(resolution,[status(thm)],[c_88,c_177])).

tff(c_181,plain,(
    ! [B_72,D_74] : k7_relset_1('#skF_4',B_72,'#skF_4',D_74) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_179])).

tff(c_22,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_22])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:48:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.30  
% 1.98/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k4_mcart_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.98/1.30  
% 1.98/1.30  %Foreground sorts:
% 1.98/1.30  
% 1.98/1.30  
% 1.98/1.30  %Background operators:
% 1.98/1.30  
% 1.98/1.30  
% 1.98/1.30  %Foreground operators:
% 1.98/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.98/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.30  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 1.98/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.30  
% 1.98/1.31  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 1.98/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.31  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.98/1.31  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_2)).
% 1.98/1.31  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.98/1.31  tff(f_41, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.98/1.31  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.98/1.31  tff(c_16, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.31  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.31  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.31  tff(c_29, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 1.98/1.31  tff(c_71, plain, (![C_35, B_36, A_37]: (~v1_xboole_0(C_35) | ~m1_subset_1(B_36, k1_zfmisc_1(C_35)) | ~r2_hidden(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.31  tff(c_73, plain, (![A_37]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_37, '#skF_4'))), inference(resolution, [status(thm)], [c_29, c_71])).
% 1.98/1.31  tff(c_77, plain, (![A_38]: (~r2_hidden(A_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_73])).
% 1.98/1.31  tff(c_82, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16, c_77])).
% 1.98/1.31  tff(c_12, plain, (![A_6]: (k9_relat_1(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.31  tff(c_86, plain, (![A_6]: (k9_relat_1('#skF_4', A_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_12])).
% 1.98/1.31  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_29])).
% 1.98/1.31  tff(c_89, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_8])).
% 1.98/1.31  tff(c_159, plain, (![A_59, B_60, C_61, D_62]: (k7_relset_1(A_59, B_60, C_61, D_62)=k9_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.31  tff(c_177, plain, (![B_72, C_73, D_74]: (k7_relset_1('#skF_4', B_72, C_73, D_74)=k9_relat_1(C_73, D_74) | ~m1_subset_1(C_73, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_159])).
% 1.98/1.31  tff(c_179, plain, (![B_72, D_74]: (k7_relset_1('#skF_4', B_72, '#skF_4', D_74)=k9_relat_1('#skF_4', D_74))), inference(resolution, [status(thm)], [c_88, c_177])).
% 1.98/1.31  tff(c_181, plain, (![B_72, D_74]: (k7_relset_1('#skF_4', B_72, '#skF_4', D_74)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_179])).
% 1.98/1.31  tff(c_22, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.31  tff(c_84, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_22])).
% 1.98/1.31  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_84])).
% 1.98/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.31  
% 1.98/1.31  Inference rules
% 1.98/1.31  ----------------------
% 1.98/1.31  #Ref     : 0
% 1.98/1.31  #Sup     : 34
% 1.98/1.31  #Fact    : 0
% 1.98/1.31  #Define  : 0
% 1.98/1.31  #Split   : 0
% 1.98/1.31  #Chain   : 0
% 1.98/1.31  #Close   : 0
% 1.98/1.31  
% 1.98/1.31  Ordering : KBO
% 1.98/1.31  
% 1.98/1.31  Simplification rules
% 1.98/1.31  ----------------------
% 1.98/1.31  #Subsume      : 1
% 1.98/1.31  #Demod        : 23
% 1.98/1.31  #Tautology    : 25
% 1.98/1.31  #SimpNegUnit  : 0
% 1.98/1.31  #BackRed      : 10
% 1.98/1.31  
% 1.98/1.31  #Partial instantiations: 0
% 1.98/1.31  #Strategies tried      : 1
% 1.98/1.31  
% 1.98/1.31  Timing (in seconds)
% 1.98/1.31  ----------------------
% 1.98/1.31  Preprocessing        : 0.35
% 1.98/1.31  Parsing              : 0.17
% 1.98/1.31  CNF conversion       : 0.02
% 1.98/1.31  Main loop            : 0.15
% 1.98/1.31  Inferencing          : 0.05
% 1.98/1.31  Reduction            : 0.05
% 1.98/1.31  Demodulation         : 0.04
% 1.98/1.31  BG Simplification    : 0.01
% 1.98/1.31  Subsumption          : 0.02
% 1.98/1.31  Abstraction          : 0.01
% 1.98/1.31  MUC search           : 0.00
% 1.98/1.31  Cooper               : 0.00
% 1.98/1.31  Total                : 0.53
% 1.98/1.31  Index Insertion      : 0.00
% 1.98/1.31  Index Deletion       : 0.00
% 1.98/1.32  Index Matching       : 0.00
% 1.98/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
