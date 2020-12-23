%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:08 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 108 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 186 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_18,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_31,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_67,plain,(
    ! [C_30,B_31,A_32] :
      ( ~ v1_xboole_0(C_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_31,c_67])).

tff(c_76,plain,(
    ! [A_33] : ~ r2_hidden(A_33,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_90,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_10])).

tff(c_84,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | A_14 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_18])).

tff(c_162,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( m1_subset_1(k8_relset_1(A_53,B_54,C_55,D_56),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_169,plain,(
    ! [A_58,A_59,C_57,B_61,D_60] :
      ( ~ v1_xboole_0(A_58)
      | ~ r2_hidden(A_59,k8_relset_1(A_58,B_61,C_57,D_60))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_61))) ) ),
    inference(resolution,[status(thm)],[c_162,c_14])).

tff(c_174,plain,(
    ! [A_62,C_63,B_64,D_65] :
      ( ~ v1_xboole_0(A_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_62,B_64)))
      | k8_relset_1(A_62,B_64,C_63,D_65) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_84,c_169])).

tff(c_189,plain,(
    ! [A_66,B_67,D_68] :
      ( ~ v1_xboole_0(A_66)
      | k8_relset_1(A_66,B_67,'#skF_4',D_68) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_88,c_174])).

tff(c_192,plain,(
    ! [B_67,D_68] : k8_relset_1('#skF_4',B_67,'#skF_4',D_68) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_90,c_189])).

tff(c_24,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_24])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.18  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.94/1.18  
% 1.94/1.18  %Foreground sorts:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Background operators:
% 1.94/1.18  
% 1.94/1.18  
% 1.94/1.18  %Foreground operators:
% 1.94/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.18  
% 1.94/1.19  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 1.94/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.19  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.94/1.19  tff(f_76, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.94/1.19  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.94/1.19  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.94/1.19  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.94/1.19  tff(c_18, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.19  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.19  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.19  tff(c_31, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 1.94/1.19  tff(c_67, plain, (![C_30, B_31, A_32]: (~v1_xboole_0(C_30) | ~m1_subset_1(B_31, k1_zfmisc_1(C_30)) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.19  tff(c_69, plain, (![A_32]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_32, '#skF_4'))), inference(resolution, [status(thm)], [c_31, c_67])).
% 1.94/1.19  tff(c_76, plain, (![A_33]: (~r2_hidden(A_33, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_69])).
% 1.94/1.19  tff(c_81, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_76])).
% 1.94/1.19  tff(c_90, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2])).
% 1.94/1.19  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.94/1.19  tff(c_88, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_10])).
% 1.94/1.19  tff(c_84, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | A_14='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_18])).
% 1.94/1.19  tff(c_162, plain, (![A_53, B_54, C_55, D_56]: (m1_subset_1(k8_relset_1(A_53, B_54, C_55, D_56), k1_zfmisc_1(A_53)) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.19  tff(c_14, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.19  tff(c_169, plain, (![A_58, A_59, C_57, B_61, D_60]: (~v1_xboole_0(A_58) | ~r2_hidden(A_59, k8_relset_1(A_58, B_61, C_57, D_60)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_61))))), inference(resolution, [status(thm)], [c_162, c_14])).
% 1.94/1.19  tff(c_174, plain, (![A_62, C_63, B_64, D_65]: (~v1_xboole_0(A_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_62, B_64))) | k8_relset_1(A_62, B_64, C_63, D_65)='#skF_4')), inference(resolution, [status(thm)], [c_84, c_169])).
% 1.94/1.19  tff(c_189, plain, (![A_66, B_67, D_68]: (~v1_xboole_0(A_66) | k8_relset_1(A_66, B_67, '#skF_4', D_68)='#skF_4')), inference(resolution, [status(thm)], [c_88, c_174])).
% 1.94/1.19  tff(c_192, plain, (![B_67, D_68]: (k8_relset_1('#skF_4', B_67, '#skF_4', D_68)='#skF_4')), inference(resolution, [status(thm)], [c_90, c_189])).
% 1.94/1.19  tff(c_24, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.19  tff(c_83, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_24])).
% 1.94/1.19  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_83])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 35
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 0
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 4
% 1.94/1.19  #Demod        : 23
% 1.94/1.19  #Tautology    : 20
% 1.94/1.19  #SimpNegUnit  : 0
% 1.94/1.19  #BackRed      : 10
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.20  Preprocessing        : 0.27
% 1.94/1.20  Parsing              : 0.15
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.16
% 1.94/1.20  Inferencing          : 0.06
% 1.94/1.20  Reduction            : 0.05
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.03
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.46
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
