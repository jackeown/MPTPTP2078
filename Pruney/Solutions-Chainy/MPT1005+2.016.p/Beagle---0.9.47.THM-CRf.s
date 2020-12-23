%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 116 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 174 expanded)
%              Number of equality atoms :   17 (  50 expanded)
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_87,plain,(
    ! [C_30,B_31,A_32] :
      ( ~ v1_xboole_0(C_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_33,c_87])).

tff(c_96,plain,(
    ! [A_33] : ~ r2_hidden(A_33,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_101,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_96])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_22,plain,(
    ! [A_15] : k9_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,(
    ! [A_15] : k9_relat_1('#skF_4',A_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_22])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_120,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_179,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k7_relset_1(A_42,B_43,C_44,D_45) = k9_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_182,plain,(
    ! [A_42,B_43,D_45] : k7_relset_1(A_42,B_43,'#skF_4',D_45) = k9_relat_1('#skF_4',D_45) ),
    inference(resolution,[status(thm)],[c_120,c_179])).

tff(c_188,plain,(
    ! [A_42,B_43,D_45] : k7_relset_1(A_42,B_43,'#skF_4',D_45) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_182])).

tff(c_26,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_114,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_26])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.18  
% 1.95/1.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.95/1.19  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.95/1.19  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.95/1.19  tff(f_72, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.95/1.19  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.95/1.19  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.95/1.19  tff(f_59, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.95/1.19  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.95/1.19  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.95/1.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.19  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.19  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.95/1.19  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.19  tff(c_33, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 1.95/1.19  tff(c_87, plain, (![C_30, B_31, A_32]: (~v1_xboole_0(C_30) | ~m1_subset_1(B_31, k1_zfmisc_1(C_30)) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.19  tff(c_89, plain, (![A_32]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_32, '#skF_4'))), inference(resolution, [status(thm)], [c_33, c_87])).
% 1.95/1.19  tff(c_96, plain, (![A_33]: (~r2_hidden(A_33, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_89])).
% 1.95/1.19  tff(c_101, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_96])).
% 1.95/1.19  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.95/1.19  tff(c_112, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_101, c_8])).
% 1.95/1.19  tff(c_22, plain, (![A_15]: (k9_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.19  tff(c_117, plain, (![A_15]: (k9_relat_1('#skF_4', A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_22])).
% 1.95/1.19  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.19  tff(c_120, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_16])).
% 1.95/1.19  tff(c_179, plain, (![A_42, B_43, C_44, D_45]: (k7_relset_1(A_42, B_43, C_44, D_45)=k9_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.95/1.19  tff(c_182, plain, (![A_42, B_43, D_45]: (k7_relset_1(A_42, B_43, '#skF_4', D_45)=k9_relat_1('#skF_4', D_45))), inference(resolution, [status(thm)], [c_120, c_179])).
% 1.95/1.19  tff(c_188, plain, (![A_42, B_43, D_45]: (k7_relset_1(A_42, B_43, '#skF_4', D_45)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_182])).
% 1.95/1.19  tff(c_26, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.95/1.19  tff(c_114, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_26])).
% 1.95/1.19  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_114])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 38
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 0
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 7
% 1.95/1.19  #Demod        : 25
% 1.95/1.19  #Tautology    : 27
% 1.95/1.19  #SimpNegUnit  : 0
% 1.95/1.19  #BackRed      : 11
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.29
% 1.95/1.19  Parsing              : 0.16
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.14
% 1.95/1.19  Inferencing          : 0.05
% 1.95/1.19  Reduction            : 0.05
% 1.95/1.19  Demodulation         : 0.03
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.02
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.46
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
