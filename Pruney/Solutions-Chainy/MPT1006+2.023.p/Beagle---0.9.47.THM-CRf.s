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
% DateTime   : Thu Dec  3 10:14:05 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 144 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 ( 247 expanded)
%              Number of equality atoms :   13 (  87 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [C_28,B_29,A_30] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(B_29,A_30)))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [C_28] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_92,plain,(
    ! [C_31] :
      ( v1_xboole_0(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_102,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_27,c_92])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_12])).

tff(c_103,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(k8_relset_1(A_32,B_33,C_34,D_35),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [C_28] :
      ( v1_xboole_0(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_107,plain,(
    ! [B_33,C_34,D_35] :
      ( v1_xboole_0(k8_relset_1(k1_xboole_0,B_33,C_34,D_35))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(resolution,[status(thm)],[c_103,c_91])).

tff(c_115,plain,(
    ! [B_33,C_34,D_35] :
      ( v1_xboole_0(k8_relset_1(k1_xboole_0,B_33,C_34,D_35))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_222,plain,(
    ! [B_50,C_51,D_52] :
      ( v1_xboole_0(k8_relset_1('#skF_3',B_50,C_51,D_52))
      | ~ m1_subset_1(C_51,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_115])).

tff(c_232,plain,(
    ! [B_53,D_54] : v1_xboole_0(k8_relset_1('#skF_3',B_53,'#skF_3',D_54)) ),
    inference(resolution,[status(thm)],[c_128,c_222])).

tff(c_127,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_236,plain,(
    ! [B_53,D_54] : k8_relset_1('#skF_3',B_53,'#skF_3',D_54) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_232,c_127])).

tff(c_20,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_20])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:33:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.29  
% 1.98/1.29  %Foreground sorts:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Background operators:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Foreground operators:
% 1.98/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.98/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.29  
% 1.98/1.30  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.98/1.30  tff(f_64, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 1.98/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.30  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.98/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.98/1.30  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.98/1.30  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.98/1.30  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.30  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.30  tff(c_27, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 1.98/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.30  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.30  tff(c_77, plain, (![C_28, B_29, A_30]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(B_29, A_30))) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.30  tff(c_84, plain, (![C_28]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_77])).
% 1.98/1.30  tff(c_92, plain, (![C_31]: (v1_xboole_0(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_84])).
% 1.98/1.30  tff(c_102, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_27, c_92])).
% 1.98/1.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.98/1.30  tff(c_121, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_102, c_4])).
% 1.98/1.30  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.30  tff(c_128, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_12])).
% 1.98/1.30  tff(c_103, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(k8_relset_1(A_32, B_33, C_34, D_35), k1_zfmisc_1(A_32)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.98/1.30  tff(c_91, plain, (![C_28]: (v1_xboole_0(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_84])).
% 1.98/1.30  tff(c_107, plain, (![B_33, C_34, D_35]: (v1_xboole_0(k8_relset_1(k1_xboole_0, B_33, C_34, D_35)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(resolution, [status(thm)], [c_103, c_91])).
% 1.98/1.30  tff(c_115, plain, (![B_33, C_34, D_35]: (v1_xboole_0(k8_relset_1(k1_xboole_0, B_33, C_34, D_35)) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_107])).
% 1.98/1.30  tff(c_222, plain, (![B_50, C_51, D_52]: (v1_xboole_0(k8_relset_1('#skF_3', B_50, C_51, D_52)) | ~m1_subset_1(C_51, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_115])).
% 1.98/1.30  tff(c_232, plain, (![B_53, D_54]: (v1_xboole_0(k8_relset_1('#skF_3', B_53, '#skF_3', D_54)))), inference(resolution, [status(thm)], [c_128, c_222])).
% 1.98/1.30  tff(c_127, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4])).
% 1.98/1.30  tff(c_236, plain, (![B_53, D_54]: (k8_relset_1('#skF_3', B_53, '#skF_3', D_54)='#skF_3')), inference(resolution, [status(thm)], [c_232, c_127])).
% 1.98/1.30  tff(c_20, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.30  tff(c_126, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_20])).
% 1.98/1.30  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_126])).
% 1.98/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.30  
% 1.98/1.30  Inference rules
% 1.98/1.30  ----------------------
% 1.98/1.30  #Ref     : 0
% 1.98/1.30  #Sup     : 46
% 1.98/1.30  #Fact    : 0
% 1.98/1.30  #Define  : 0
% 1.98/1.30  #Split   : 1
% 1.98/1.30  #Chain   : 0
% 1.98/1.30  #Close   : 0
% 1.98/1.30  
% 1.98/1.30  Ordering : KBO
% 1.98/1.30  
% 1.98/1.30  Simplification rules
% 1.98/1.30  ----------------------
% 1.98/1.30  #Subsume      : 10
% 1.98/1.30  #Demod        : 40
% 1.98/1.30  #Tautology    : 27
% 1.98/1.30  #SimpNegUnit  : 2
% 1.98/1.30  #BackRed      : 15
% 1.98/1.30  
% 1.98/1.30  #Partial instantiations: 0
% 1.98/1.30  #Strategies tried      : 1
% 1.98/1.30  
% 1.98/1.30  Timing (in seconds)
% 1.98/1.30  ----------------------
% 1.98/1.30  Preprocessing        : 0.29
% 1.98/1.30  Parsing              : 0.16
% 1.98/1.30  CNF conversion       : 0.02
% 1.98/1.30  Main loop            : 0.19
% 1.98/1.30  Inferencing          : 0.07
% 1.98/1.30  Reduction            : 0.06
% 1.98/1.30  Demodulation         : 0.04
% 1.98/1.30  BG Simplification    : 0.01
% 1.98/1.30  Subsumption          : 0.04
% 1.98/1.30  Abstraction          : 0.01
% 1.98/1.30  MUC search           : 0.00
% 1.98/1.30  Cooper               : 0.00
% 1.98/1.30  Total                : 0.51
% 1.98/1.30  Index Insertion      : 0.00
% 1.98/1.30  Index Deletion       : 0.00
% 1.98/1.30  Index Matching       : 0.00
% 1.98/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
