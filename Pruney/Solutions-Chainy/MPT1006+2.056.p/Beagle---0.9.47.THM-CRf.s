%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 136 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 231 expanded)
%              Number of equality atoms :   18 (  71 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_mcart_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_72,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_35,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_77,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_49,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_35,c_77])).

tff(c_86,plain,(
    ! [A_50] : ~ r2_hidden(A_50,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_91,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_181,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k8_relset_1(A_79,B_80,C_81,D_82) = k10_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_189,plain,(
    ! [A_79,B_80,D_82] : k8_relset_1(A_79,B_80,'#skF_4',D_82) = k10_relat_1('#skF_4',D_82) ),
    inference(resolution,[status(thm)],[c_98,c_181])).

tff(c_206,plain,(
    ! [A_89,B_90,D_91,C_92] :
      ( r1_tarski(k8_relset_1(A_89,B_90,D_91,C_92),A_89)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_1(D_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_211,plain,(
    ! [A_89,B_90,C_92] :
      ( r1_tarski(k8_relset_1(A_89,B_90,'#skF_4',C_92),A_89)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_98,c_206])).

tff(c_217,plain,(
    ! [C_93,A_94] : r1_tarski(k10_relat_1('#skF_4',C_93),A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_189,c_211])).

tff(c_60,plain,(
    ! [B_42,A_43] :
      ( ~ r1_tarski(B_42,A_43)
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    ! [A_16] :
      ( ~ r1_tarski(A_16,'#skF_1'(A_16))
      | k1_xboole_0 = A_16 ) ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_93,plain,(
    ! [A_16] :
      ( ~ r1_tarski(A_16,'#skF_1'(A_16))
      | A_16 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64])).

tff(c_222,plain,(
    ! [C_93] : k10_relat_1('#skF_4',C_93) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_217,c_93])).

tff(c_28,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_95,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_28])).

tff(c_190,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_95])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_mcart_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.04/1.24  
% 2.04/1.24  %Foreground sorts:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Background operators:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Foreground operators:
% 2.04/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.04/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.04/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.04/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.24  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.04/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.24  
% 2.04/1.25  tff(f_87, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.04/1.25  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.04/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.04/1.25  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.04/1.25  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.04/1.25  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.04/1.25  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.04/1.25  tff(f_78, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 2.04/1.25  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.04/1.25  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.25  tff(c_20, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.04/1.25  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.25  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.25  tff(c_35, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_30])).
% 2.04/1.25  tff(c_77, plain, (![C_47, B_48, A_49]: (~v1_xboole_0(C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.25  tff(c_79, plain, (![A_49]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_35, c_77])).
% 2.04/1.25  tff(c_86, plain, (![A_50]: (~r2_hidden(A_50, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_79])).
% 2.04/1.25  tff(c_91, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.04/1.25  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.25  tff(c_98, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_10])).
% 2.04/1.25  tff(c_181, plain, (![A_79, B_80, C_81, D_82]: (k8_relset_1(A_79, B_80, C_81, D_82)=k10_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.25  tff(c_189, plain, (![A_79, B_80, D_82]: (k8_relset_1(A_79, B_80, '#skF_4', D_82)=k10_relat_1('#skF_4', D_82))), inference(resolution, [status(thm)], [c_98, c_181])).
% 2.04/1.25  tff(c_206, plain, (![A_89, B_90, D_91, C_92]: (r1_tarski(k8_relset_1(A_89, B_90, D_91, C_92), A_89) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_1(D_91))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.04/1.25  tff(c_211, plain, (![A_89, B_90, C_92]: (r1_tarski(k8_relset_1(A_89, B_90, '#skF_4', C_92), A_89) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_98, c_206])).
% 2.04/1.25  tff(c_217, plain, (![C_93, A_94]: (r1_tarski(k10_relat_1('#skF_4', C_93), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_189, c_211])).
% 2.04/1.25  tff(c_60, plain, (![B_42, A_43]: (~r1_tarski(B_42, A_43) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.25  tff(c_64, plain, (![A_16]: (~r1_tarski(A_16, '#skF_1'(A_16)) | k1_xboole_0=A_16)), inference(resolution, [status(thm)], [c_20, c_60])).
% 2.04/1.25  tff(c_93, plain, (![A_16]: (~r1_tarski(A_16, '#skF_1'(A_16)) | A_16='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64])).
% 2.04/1.25  tff(c_222, plain, (![C_93]: (k10_relat_1('#skF_4', C_93)='#skF_4')), inference(resolution, [status(thm)], [c_217, c_93])).
% 2.04/1.25  tff(c_28, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.25  tff(c_95, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_28])).
% 2.04/1.25  tff(c_190, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_95])).
% 2.04/1.25  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_190])).
% 2.04/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  Inference rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Ref     : 0
% 2.04/1.25  #Sup     : 40
% 2.04/1.25  #Fact    : 0
% 2.04/1.25  #Define  : 0
% 2.04/1.25  #Split   : 0
% 2.04/1.26  #Chain   : 0
% 2.04/1.26  #Close   : 0
% 2.04/1.26  
% 2.04/1.26  Ordering : KBO
% 2.04/1.26  
% 2.04/1.26  Simplification rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Subsume      : 6
% 2.04/1.26  #Demod        : 29
% 2.04/1.26  #Tautology    : 23
% 2.04/1.26  #SimpNegUnit  : 0
% 2.04/1.26  #BackRed      : 14
% 2.04/1.26  
% 2.04/1.26  #Partial instantiations: 0
% 2.04/1.26  #Strategies tried      : 1
% 2.04/1.26  
% 2.04/1.26  Timing (in seconds)
% 2.04/1.26  ----------------------
% 2.04/1.26  Preprocessing        : 0.30
% 2.04/1.26  Parsing              : 0.17
% 2.04/1.26  CNF conversion       : 0.02
% 2.04/1.26  Main loop            : 0.15
% 2.04/1.26  Inferencing          : 0.06
% 2.04/1.26  Reduction            : 0.05
% 2.04/1.26  Demodulation         : 0.04
% 2.04/1.26  BG Simplification    : 0.01
% 2.04/1.26  Subsumption          : 0.02
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.49
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
