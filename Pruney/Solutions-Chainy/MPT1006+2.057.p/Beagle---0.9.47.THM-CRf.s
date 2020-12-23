%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:10 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 264 expanded)
%              Number of leaves         :   28 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 438 expanded)
%              Number of equality atoms :   32 ( 196 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

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

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_33,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_65,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33,c_65])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_33])).

tff(c_79,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_8])).

tff(c_166,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k8_relset_1(A_33,B_34,C_35,D_36) = k10_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_254,plain,(
    ! [B_59,C_60,D_61] :
      ( k8_relset_1('#skF_3',B_59,C_60,D_61) = k10_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_166])).

tff(c_260,plain,(
    ! [B_59,D_61] : k8_relset_1('#skF_3',B_59,'#skF_3',D_61) = k10_relat_1('#skF_3',D_61) ),
    inference(resolution,[status(thm)],[c_78,c_254])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_16])).

tff(c_145,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_157,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1('#skF_3',B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_145])).

tff(c_159,plain,(
    ! [B_31] : k1_relset_1('#skF_3',B_31,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_157])).

tff(c_164,plain,(
    ! [B_31] : k1_relset_1('#skF_3',B_31,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_159])).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_69])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,(
    ! [A_56,B_57,C_58] :
      ( k8_relset_1(A_56,B_57,C_58,B_57) = k1_relset_1(A_56,B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_323,plain,(
    ! [A_79,B_80,A_81] :
      ( k8_relset_1(A_79,B_80,A_81,B_80) = k1_relset_1(A_79,B_80,A_81)
      | ~ r1_tarski(A_81,k2_zfmisc_1(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_12,c_245])).

tff(c_328,plain,(
    ! [B_82,A_83] :
      ( k8_relset_1('#skF_3',B_82,A_83,B_82) = k1_relset_1('#skF_3',B_82,A_83)
      | ~ r1_tarski(A_83,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_323])).

tff(c_330,plain,(
    ! [B_82] : k8_relset_1('#skF_3',B_82,'#skF_3',B_82) = k1_relset_1('#skF_3',B_82,'#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_328])).

tff(c_332,plain,(
    ! [B_82] : k10_relat_1('#skF_3',B_82) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_164,c_330])).

tff(c_26,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_26])).

tff(c_262,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_75])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.29  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.29  
% 2.24/1.29  %Foreground sorts:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Background operators:
% 2.24/1.29  
% 2.24/1.29  
% 2.24/1.29  %Foreground operators:
% 2.24/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.24/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.24/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.24/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.29  
% 2.24/1.30  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.24/1.30  tff(f_65, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.24/1.30  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.24/1.30  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.24/1.30  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.24/1.30  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.24/1.30  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.30  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.24/1.30  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.30  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.30  tff(c_33, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_28])).
% 2.24/1.30  tff(c_65, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.30  tff(c_69, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_65])).
% 2.24/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.30  tff(c_73, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.24/1.30  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_33])).
% 2.24/1.30  tff(c_79, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_8])).
% 2.24/1.30  tff(c_166, plain, (![A_33, B_34, C_35, D_36]: (k8_relset_1(A_33, B_34, C_35, D_36)=k10_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.30  tff(c_254, plain, (![B_59, C_60, D_61]: (k8_relset_1('#skF_3', B_59, C_60, D_61)=k10_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_166])).
% 2.24/1.30  tff(c_260, plain, (![B_59, D_61]: (k8_relset_1('#skF_3', B_59, '#skF_3', D_61)=k10_relat_1('#skF_3', D_61))), inference(resolution, [status(thm)], [c_78, c_254])).
% 2.24/1.30  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.30  tff(c_82, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_16])).
% 2.24/1.30  tff(c_145, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.30  tff(c_157, plain, (![B_31, C_32]: (k1_relset_1('#skF_3', B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_145])).
% 2.24/1.30  tff(c_159, plain, (![B_31]: (k1_relset_1('#skF_3', B_31, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_157])).
% 2.24/1.30  tff(c_164, plain, (![B_31]: (k1_relset_1('#skF_3', B_31, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_159])).
% 2.24/1.30  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_69])).
% 2.24/1.30  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.30  tff(c_245, plain, (![A_56, B_57, C_58]: (k8_relset_1(A_56, B_57, C_58, B_57)=k1_relset_1(A_56, B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.24/1.30  tff(c_323, plain, (![A_79, B_80, A_81]: (k8_relset_1(A_79, B_80, A_81, B_80)=k1_relset_1(A_79, B_80, A_81) | ~r1_tarski(A_81, k2_zfmisc_1(A_79, B_80)))), inference(resolution, [status(thm)], [c_12, c_245])).
% 2.24/1.30  tff(c_328, plain, (![B_82, A_83]: (k8_relset_1('#skF_3', B_82, A_83, B_82)=k1_relset_1('#skF_3', B_82, A_83) | ~r1_tarski(A_83, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_323])).
% 2.24/1.30  tff(c_330, plain, (![B_82]: (k8_relset_1('#skF_3', B_82, '#skF_3', B_82)=k1_relset_1('#skF_3', B_82, '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_328])).
% 2.24/1.30  tff(c_332, plain, (![B_82]: (k10_relat_1('#skF_3', B_82)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_164, c_330])).
% 2.24/1.30  tff(c_26, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.30  tff(c_75, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_26])).
% 2.24/1.30  tff(c_262, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_75])).
% 2.24/1.30  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_262])).
% 2.24/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  Inference rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Ref     : 0
% 2.24/1.30  #Sup     : 77
% 2.24/1.30  #Fact    : 0
% 2.24/1.30  #Define  : 0
% 2.24/1.30  #Split   : 0
% 2.24/1.30  #Chain   : 0
% 2.24/1.30  #Close   : 0
% 2.24/1.30  
% 2.24/1.30  Ordering : KBO
% 2.24/1.30  
% 2.24/1.30  Simplification rules
% 2.24/1.30  ----------------------
% 2.24/1.30  #Subsume      : 4
% 2.24/1.30  #Demod        : 35
% 2.24/1.30  #Tautology    : 46
% 2.24/1.30  #SimpNegUnit  : 0
% 2.24/1.30  #BackRed      : 13
% 2.24/1.30  
% 2.24/1.30  #Partial instantiations: 0
% 2.24/1.30  #Strategies tried      : 1
% 2.24/1.30  
% 2.24/1.30  Timing (in seconds)
% 2.24/1.30  ----------------------
% 2.24/1.30  Preprocessing        : 0.32
% 2.24/1.30  Parsing              : 0.17
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.22
% 2.24/1.30  Inferencing          : 0.08
% 2.24/1.30  Reduction            : 0.07
% 2.24/1.31  Demodulation         : 0.05
% 2.24/1.31  BG Simplification    : 0.01
% 2.24/1.31  Subsumption          : 0.03
% 2.24/1.31  Abstraction          : 0.02
% 2.24/1.31  MUC search           : 0.00
% 2.24/1.31  Cooper               : 0.00
% 2.24/1.31  Total                : 0.57
% 2.24/1.31  Index Insertion      : 0.00
% 2.24/1.31  Index Deletion       : 0.00
% 2.24/1.31  Index Matching       : 0.00
% 2.24/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
