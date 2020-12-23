%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:08 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 107 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 ( 168 expanded)
%              Number of equality atoms :   14 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

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

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_27,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_63,plain,(
    ! [C_22,B_23,A_24] :
      ( ~ v1_xboole_0(C_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_27,c_63])).

tff(c_72,plain,(
    ! [A_25] : ~ r2_hidden(A_25,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_86,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_12])).

tff(c_79,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_4])).

tff(c_149,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( m1_subset_1(k8_relset_1(A_35,B_36,C_37,D_38),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [B_43,D_41,A_42,A_39,C_40] :
      ( ~ v1_xboole_0(A_39)
      | ~ r2_hidden(A_42,k8_relset_1(A_39,B_43,C_40,D_41))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_39,B_43))) ) ),
    inference(resolution,[status(thm)],[c_149,c_16])).

tff(c_161,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( ~ v1_xboole_0(A_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_44,B_46)))
      | k8_relset_1(A_44,B_46,C_45,D_47) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_79,c_156])).

tff(c_176,plain,(
    ! [A_48,B_49,D_50] :
      ( ~ v1_xboole_0(A_48)
      | k8_relset_1(A_48,B_49,'#skF_4',D_50) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_81,c_161])).

tff(c_179,plain,(
    ! [B_49,D_50] : k8_relset_1('#skF_4',B_49,'#skF_4',D_50) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_86,c_176])).

tff(c_20,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_20])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:26:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.24  
% 1.93/1.25  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.93/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.93/1.25  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.93/1.25  tff(f_68, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.93/1.25  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.93/1.25  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.93/1.25  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.93/1.25  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.93/1.25  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.25  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.25  tff(c_27, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 1.93/1.25  tff(c_63, plain, (![C_22, B_23, A_24]: (~v1_xboole_0(C_22) | ~m1_subset_1(B_23, k1_zfmisc_1(C_22)) | ~r2_hidden(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.25  tff(c_67, plain, (![A_24]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_24, '#skF_4'))), inference(resolution, [status(thm)], [c_27, c_63])).
% 1.93/1.25  tff(c_72, plain, (![A_25]: (~r2_hidden(A_25, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_67])).
% 1.93/1.25  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_72])).
% 1.93/1.25  tff(c_86, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2])).
% 1.93/1.25  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.25  tff(c_81, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_12])).
% 1.93/1.25  tff(c_79, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_4])).
% 1.93/1.25  tff(c_149, plain, (![A_35, B_36, C_37, D_38]: (m1_subset_1(k8_relset_1(A_35, B_36, C_37, D_38), k1_zfmisc_1(A_35)) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.25  tff(c_16, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.25  tff(c_156, plain, (![B_43, D_41, A_42, A_39, C_40]: (~v1_xboole_0(A_39) | ~r2_hidden(A_42, k8_relset_1(A_39, B_43, C_40, D_41)) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_39, B_43))))), inference(resolution, [status(thm)], [c_149, c_16])).
% 1.93/1.25  tff(c_161, plain, (![A_44, C_45, B_46, D_47]: (~v1_xboole_0(A_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_44, B_46))) | k8_relset_1(A_44, B_46, C_45, D_47)='#skF_4')), inference(resolution, [status(thm)], [c_79, c_156])).
% 1.93/1.25  tff(c_176, plain, (![A_48, B_49, D_50]: (~v1_xboole_0(A_48) | k8_relset_1(A_48, B_49, '#skF_4', D_50)='#skF_4')), inference(resolution, [status(thm)], [c_81, c_161])).
% 1.93/1.25  tff(c_179, plain, (![B_49, D_50]: (k8_relset_1('#skF_4', B_49, '#skF_4', D_50)='#skF_4')), inference(resolution, [status(thm)], [c_86, c_176])).
% 1.93/1.25  tff(c_20, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.25  tff(c_80, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_20])).
% 1.93/1.25  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_80])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 34
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 0
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 5
% 1.93/1.25  #Demod        : 21
% 1.93/1.25  #Tautology    : 20
% 1.93/1.25  #SimpNegUnit  : 0
% 1.93/1.25  #BackRed      : 10
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.25  Preprocessing        : 0.28
% 1.93/1.25  Parsing              : 0.16
% 1.93/1.25  CNF conversion       : 0.02
% 1.93/1.25  Main loop            : 0.15
% 1.93/1.25  Inferencing          : 0.06
% 1.93/1.25  Reduction            : 0.05
% 1.93/1.25  Demodulation         : 0.03
% 1.93/1.25  BG Simplification    : 0.01
% 1.93/1.25  Subsumption          : 0.02
% 1.93/1.25  Abstraction          : 0.01
% 1.93/1.25  MUC search           : 0.00
% 1.93/1.25  Cooper               : 0.00
% 1.93/1.25  Total                : 0.46
% 1.93/1.25  Index Insertion      : 0.00
% 1.93/1.25  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
