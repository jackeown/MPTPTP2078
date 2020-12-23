%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 209 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :   46 ( 349 expanded)
%              Number of equality atoms :   18 ( 150 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_50,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25,c_50])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_67,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25])).

tff(c_68,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_8])).

tff(c_119,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k7_relset_1(A_26,B_27,C_28,D_29) = k9_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150,plain,(
    ! [B_38,C_39,D_40] :
      ( k7_relset_1('#skF_3',B_38,C_39,D_40) = k9_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_119])).

tff(c_156,plain,(
    ! [B_38,D_40] : k7_relset_1('#skF_3',B_38,'#skF_3',D_40) = k9_relat_1('#skF_3',D_40) ),
    inference(resolution,[status(thm)],[c_67,c_150])).

tff(c_178,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( m1_subset_1(k7_relset_1(A_43,B_44,C_45,D_46),k1_zfmisc_1(B_44))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_193,plain,(
    ! [D_40,B_38] :
      ( m1_subset_1(k9_relat_1('#skF_3',D_40),k1_zfmisc_1(B_38))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_38))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_178])).

tff(c_207,plain,(
    ! [D_47,B_48] : m1_subset_1(k9_relat_1('#skF_3',D_47),k1_zfmisc_1(B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_68,c_193])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,(
    ! [D_49,B_50] : r1_tarski(k9_relat_1('#skF_3',D_49),B_50) ),
    inference(resolution,[status(thm)],[c_207,c_10])).

tff(c_65,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ r1_tarski(A_1,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_2])).

tff(c_233,plain,(
    ! [D_49] : k9_relat_1('#skF_3',D_49) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_224,c_65])).

tff(c_18,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_18])).

tff(c_158,plain,(
    k9_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_64])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.17  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.17  
% 1.65/1.17  %Foreground sorts:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Background operators:
% 1.65/1.17  
% 1.65/1.17  
% 1.65/1.17  %Foreground operators:
% 1.65/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.65/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.65/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.17  
% 1.92/1.19  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.19  tff(f_56, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.92/1.19  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.92/1.19  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.92/1.19  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.92/1.19  tff(f_43, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 1.92/1.19  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.19  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.19  tff(c_25, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 1.92/1.19  tff(c_50, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.19  tff(c_58, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_25, c_50])).
% 1.92/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.19  tff(c_62, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.92/1.19  tff(c_67, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25])).
% 1.92/1.19  tff(c_68, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_8])).
% 1.92/1.19  tff(c_119, plain, (![A_26, B_27, C_28, D_29]: (k7_relset_1(A_26, B_27, C_28, D_29)=k9_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.19  tff(c_150, plain, (![B_38, C_39, D_40]: (k7_relset_1('#skF_3', B_38, C_39, D_40)=k9_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_119])).
% 1.92/1.19  tff(c_156, plain, (![B_38, D_40]: (k7_relset_1('#skF_3', B_38, '#skF_3', D_40)=k9_relat_1('#skF_3', D_40))), inference(resolution, [status(thm)], [c_67, c_150])).
% 1.92/1.19  tff(c_178, plain, (![A_43, B_44, C_45, D_46]: (m1_subset_1(k7_relset_1(A_43, B_44, C_45, D_46), k1_zfmisc_1(B_44)) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.19  tff(c_193, plain, (![D_40, B_38]: (m1_subset_1(k9_relat_1('#skF_3', D_40), k1_zfmisc_1(B_38)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_38))))), inference(superposition, [status(thm), theory('equality')], [c_156, c_178])).
% 1.92/1.19  tff(c_207, plain, (![D_47, B_48]: (m1_subset_1(k9_relat_1('#skF_3', D_47), k1_zfmisc_1(B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_68, c_193])).
% 1.92/1.19  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.19  tff(c_224, plain, (![D_49, B_50]: (r1_tarski(k9_relat_1('#skF_3', D_49), B_50))), inference(resolution, [status(thm)], [c_207, c_10])).
% 1.92/1.19  tff(c_65, plain, (![A_1]: (A_1='#skF_3' | ~r1_tarski(A_1, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_2])).
% 1.92/1.19  tff(c_233, plain, (![D_49]: (k9_relat_1('#skF_3', D_49)='#skF_3')), inference(resolution, [status(thm)], [c_224, c_65])).
% 1.92/1.19  tff(c_18, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.19  tff(c_64, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_18])).
% 1.92/1.19  tff(c_158, plain, (k9_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_64])).
% 1.92/1.19  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_158])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 47
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 0
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 0
% 1.92/1.19  #Demod        : 30
% 1.92/1.19  #Tautology    : 27
% 1.92/1.19  #SimpNegUnit  : 0
% 1.92/1.19  #BackRed      : 13
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.28
% 1.92/1.19  Parsing              : 0.15
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.16
% 1.92/1.19  Inferencing          : 0.06
% 1.92/1.19  Reduction            : 0.05
% 1.92/1.19  Demodulation         : 0.04
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.02
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.46
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
