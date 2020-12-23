%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 182 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 326 expanded)
%              Number of equality atoms :   26 ( 126 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_41,axiom,(
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
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_22,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_38])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_43])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [B_27,A_28] :
      ( r2_hidden(B_27,A_28)
      | ~ m1_subset_1(B_27,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [B_27,A_1] :
      ( B_27 = A_1
      | ~ m1_subset_1(B_27,k1_tarski(A_1))
      | v1_xboole_0(k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_104,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ m1_subset_1(B_29,k1_tarski(A_30)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_100])).

tff(c_113,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_32,plain,(
    ! [A_11] : k10_relat_1(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [A_11] : k10_relat_1('#skF_5',A_11) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_32])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ r2_hidden(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [C_5] :
      ( m1_subset_1(C_5,k1_tarski(C_5))
      | v1_xboole_0(k1_tarski(C_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_114])).

tff(c_124,plain,(
    ! [C_5] : m1_subset_1(C_5,k1_tarski(C_5)) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_120])).

tff(c_130,plain,(
    k1_zfmisc_1('#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_22])).

tff(c_129,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_20])).

tff(c_219,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k8_relset_1(A_47,B_48,C_49,D_50) = k10_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_221,plain,(
    ! [B_8,C_49,D_50] :
      ( k8_relset_1('#skF_5',B_8,C_49,D_50) = k10_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_219])).

tff(c_230,plain,(
    ! [B_51,C_52,D_53] :
      ( k8_relset_1('#skF_5',B_51,C_52,D_53) = k10_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_221])).

tff(c_233,plain,(
    ! [B_51,D_53] : k8_relset_1('#skF_5',B_51,'#skF_5',D_53) = k10_relat_1('#skF_5',D_53) ),
    inference(resolution,[status(thm)],[c_124,c_230])).

tff(c_238,plain,(
    ! [B_51,D_53] : k8_relset_1('#skF_5',B_51,'#skF_5',D_53) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_233])).

tff(c_36,plain,(
    k8_relset_1(k1_xboole_0,'#skF_3','#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    k8_relset_1('#skF_5','#skF_3','#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_36])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 09:59:53 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.87/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.87/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.87/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.21  
% 1.87/1.22  tff(f_42, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.87/1.22  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.87/1.22  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 1.87/1.22  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.87/1.22  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.87/1.22  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.87/1.22  tff(f_57, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.87/1.22  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.87/1.22  tff(c_22, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.22  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.22  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.22  tff(c_43, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_38])).
% 1.87/1.22  tff(c_44, plain, (m1_subset_1('#skF_5', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_43])).
% 1.87/1.22  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.22  tff(c_96, plain, (![B_27, A_28]: (r2_hidden(B_27, A_28) | ~m1_subset_1(B_27, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.22  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.22  tff(c_100, plain, (![B_27, A_1]: (B_27=A_1 | ~m1_subset_1(B_27, k1_tarski(A_1)) | v1_xboole_0(k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_96, c_2])).
% 1.87/1.22  tff(c_104, plain, (![B_29, A_30]: (B_29=A_30 | ~m1_subset_1(B_29, k1_tarski(A_30)))), inference(negUnitSimplification, [status(thm)], [c_14, c_100])).
% 1.87/1.22  tff(c_113, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_104])).
% 1.87/1.22  tff(c_32, plain, (![A_11]: (k10_relat_1(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.22  tff(c_128, plain, (![A_11]: (k10_relat_1('#skF_5', A_11)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_32])).
% 1.87/1.22  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.22  tff(c_114, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~r2_hidden(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.22  tff(c_120, plain, (![C_5]: (m1_subset_1(C_5, k1_tarski(C_5)) | v1_xboole_0(k1_tarski(C_5)))), inference(resolution, [status(thm)], [c_4, c_114])).
% 1.87/1.22  tff(c_124, plain, (![C_5]: (m1_subset_1(C_5, k1_tarski(C_5)))), inference(negUnitSimplification, [status(thm)], [c_14, c_120])).
% 1.87/1.22  tff(c_130, plain, (k1_zfmisc_1('#skF_5')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_22])).
% 1.87/1.22  tff(c_129, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_20])).
% 1.87/1.22  tff(c_219, plain, (![A_47, B_48, C_49, D_50]: (k8_relset_1(A_47, B_48, C_49, D_50)=k10_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.22  tff(c_221, plain, (![B_8, C_49, D_50]: (k8_relset_1('#skF_5', B_8, C_49, D_50)=k10_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_219])).
% 1.87/1.22  tff(c_230, plain, (![B_51, C_52, D_53]: (k8_relset_1('#skF_5', B_51, C_52, D_53)=k10_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_221])).
% 1.87/1.22  tff(c_233, plain, (![B_51, D_53]: (k8_relset_1('#skF_5', B_51, '#skF_5', D_53)=k10_relat_1('#skF_5', D_53))), inference(resolution, [status(thm)], [c_124, c_230])).
% 1.87/1.22  tff(c_238, plain, (![B_51, D_53]: (k8_relset_1('#skF_5', B_51, '#skF_5', D_53)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_233])).
% 1.87/1.22  tff(c_36, plain, (k8_relset_1(k1_xboole_0, '#skF_3', '#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.22  tff(c_125, plain, (k8_relset_1('#skF_5', '#skF_3', '#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_36])).
% 1.87/1.22  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_125])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 0
% 1.87/1.22  #Sup     : 44
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 0
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 4
% 1.87/1.22  #Demod        : 22
% 1.87/1.22  #Tautology    : 29
% 1.87/1.22  #SimpNegUnit  : 2
% 1.87/1.22  #BackRed      : 8
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.23  Preprocessing        : 0.30
% 1.87/1.23  Parsing              : 0.16
% 1.87/1.23  CNF conversion       : 0.02
% 1.87/1.23  Main loop            : 0.17
% 1.87/1.23  Inferencing          : 0.06
% 1.87/1.23  Reduction            : 0.05
% 1.87/1.23  Demodulation         : 0.04
% 1.87/1.23  BG Simplification    : 0.01
% 1.87/1.23  Subsumption          : 0.04
% 1.87/1.23  Abstraction          : 0.01
% 1.87/1.23  MUC search           : 0.00
% 1.87/1.23  Cooper               : 0.00
% 1.87/1.23  Total                : 0.50
% 1.87/1.23  Index Insertion      : 0.00
% 1.87/1.23  Index Deletion       : 0.00
% 1.87/1.23  Index Matching       : 0.00
% 1.87/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
