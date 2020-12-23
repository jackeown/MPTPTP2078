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
% DateTime   : Thu Dec  3 10:14:00 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 189 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :   57 ( 307 expanded)
%              Number of equality atoms :   17 (  86 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24])).

tff(c_70,plain,(
    ! [B_25,A_26] :
      ( v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_29,c_70])).

tff(c_81,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_161,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k7_relset_1(A_39,B_40,C_41,D_42) = k9_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_183,plain,(
    ! [A_47,B_48,D_49] : k7_relset_1(A_47,B_48,'#skF_3',D_49) = k9_relat_1('#skF_3',D_49) ),
    inference(resolution,[status(thm)],[c_89,c_161])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( m1_subset_1(k7_relset_1(A_11,B_12,C_13,D_14),k1_zfmisc_1(B_12))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_189,plain,(
    ! [D_49,B_48,A_47] :
      ( m1_subset_1(k9_relat_1('#skF_3',D_49),k1_zfmisc_1(B_48))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_18])).

tff(c_197,plain,(
    ! [D_50,B_51] : m1_subset_1(k9_relat_1('#skF_3',D_50),k1_zfmisc_1(B_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_189])).

tff(c_14,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_208,plain,(
    ! [D_50,B_51] :
      ( v1_xboole_0(k9_relat_1('#skF_3',D_50))
      | ~ v1_xboole_0(B_51) ) ),
    inference(resolution,[status(thm)],[c_197,c_14])).

tff(c_209,plain,(
    ! [B_51] : ~ v1_xboole_0(B_51) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_81])).

tff(c_214,plain,(
    ! [D_52] : v1_xboole_0(k9_relat_1('#skF_3',D_52)) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_88,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_218,plain,(
    ! [D_52] : k9_relat_1('#skF_3',D_52) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_214,c_88])).

tff(c_169,plain,(
    ! [A_39,B_40,D_42] : k7_relset_1(A_39,B_40,'#skF_3',D_42) = k9_relat_1('#skF_3',D_42) ),
    inference(resolution,[status(thm)],[c_89,c_161])).

tff(c_22,plain,(
    k7_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    k7_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_22])).

tff(c_182,plain,(
    k9_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_87])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.29  
% 1.94/1.29  %Foreground sorts:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Background operators:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Foreground operators:
% 1.94/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.94/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.94/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.29  
% 1.94/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.30  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.94/1.30  tff(f_68, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 1.94/1.30  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 1.94/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.30  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.94/1.30  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.94/1.30  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 1.94/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.30  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.30  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.30  tff(c_29, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24])).
% 1.94/1.30  tff(c_70, plain, (![B_25, A_26]: (v1_xboole_0(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.30  tff(c_76, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_29, c_70])).
% 1.94/1.30  tff(c_81, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76])).
% 1.94/1.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.94/1.30  tff(c_85, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_81, c_4])).
% 1.94/1.30  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.30  tff(c_89, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_12])).
% 1.94/1.30  tff(c_161, plain, (![A_39, B_40, C_41, D_42]: (k7_relset_1(A_39, B_40, C_41, D_42)=k9_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.30  tff(c_183, plain, (![A_47, B_48, D_49]: (k7_relset_1(A_47, B_48, '#skF_3', D_49)=k9_relat_1('#skF_3', D_49))), inference(resolution, [status(thm)], [c_89, c_161])).
% 1.94/1.30  tff(c_18, plain, (![A_11, B_12, C_13, D_14]: (m1_subset_1(k7_relset_1(A_11, B_12, C_13, D_14), k1_zfmisc_1(B_12)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.30  tff(c_189, plain, (![D_49, B_48, A_47]: (m1_subset_1(k9_relat_1('#skF_3', D_49), k1_zfmisc_1(B_48)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(superposition, [status(thm), theory('equality')], [c_183, c_18])).
% 1.94/1.30  tff(c_197, plain, (![D_50, B_51]: (m1_subset_1(k9_relat_1('#skF_3', D_50), k1_zfmisc_1(B_51)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_189])).
% 1.94/1.30  tff(c_14, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.30  tff(c_208, plain, (![D_50, B_51]: (v1_xboole_0(k9_relat_1('#skF_3', D_50)) | ~v1_xboole_0(B_51))), inference(resolution, [status(thm)], [c_197, c_14])).
% 1.94/1.30  tff(c_209, plain, (![B_51]: (~v1_xboole_0(B_51))), inference(splitLeft, [status(thm)], [c_208])).
% 1.94/1.30  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_81])).
% 1.94/1.30  tff(c_214, plain, (![D_52]: (v1_xboole_0(k9_relat_1('#skF_3', D_52)))), inference(splitRight, [status(thm)], [c_208])).
% 1.94/1.30  tff(c_88, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4])).
% 1.94/1.30  tff(c_218, plain, (![D_52]: (k9_relat_1('#skF_3', D_52)='#skF_3')), inference(resolution, [status(thm)], [c_214, c_88])).
% 1.94/1.30  tff(c_169, plain, (![A_39, B_40, D_42]: (k7_relset_1(A_39, B_40, '#skF_3', D_42)=k9_relat_1('#skF_3', D_42))), inference(resolution, [status(thm)], [c_89, c_161])).
% 1.94/1.30  tff(c_22, plain, (k7_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.94/1.30  tff(c_87, plain, (k7_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_22])).
% 1.94/1.30  tff(c_182, plain, (k9_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_87])).
% 1.94/1.30  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_182])).
% 1.94/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.30  
% 1.94/1.30  Inference rules
% 1.94/1.30  ----------------------
% 1.94/1.30  #Ref     : 0
% 1.94/1.30  #Sup     : 40
% 1.94/1.30  #Fact    : 0
% 1.94/1.30  #Define  : 0
% 1.94/1.30  #Split   : 1
% 1.94/1.30  #Chain   : 0
% 1.94/1.30  #Close   : 0
% 1.94/1.30  
% 1.94/1.30  Ordering : KBO
% 1.94/1.30  
% 1.94/1.30  Simplification rules
% 1.94/1.30  ----------------------
% 1.94/1.30  #Subsume      : 3
% 1.94/1.30  #Demod        : 30
% 1.94/1.30  #Tautology    : 29
% 1.94/1.30  #SimpNegUnit  : 2
% 1.94/1.30  #BackRed      : 15
% 1.94/1.30  
% 1.94/1.30  #Partial instantiations: 0
% 1.94/1.30  #Strategies tried      : 1
% 1.94/1.30  
% 1.94/1.30  Timing (in seconds)
% 1.94/1.30  ----------------------
% 1.94/1.31  Preprocessing        : 0.30
% 1.94/1.31  Parsing              : 0.16
% 1.94/1.31  CNF conversion       : 0.02
% 1.94/1.31  Main loop            : 0.22
% 1.94/1.31  Inferencing          : 0.06
% 1.94/1.31  Reduction            : 0.08
% 1.94/1.31  Demodulation         : 0.06
% 1.94/1.31  BG Simplification    : 0.01
% 1.94/1.31  Subsumption          : 0.05
% 1.94/1.31  Abstraction          : 0.01
% 1.94/1.31  MUC search           : 0.00
% 1.94/1.31  Cooper               : 0.00
% 1.94/1.31  Total                : 0.55
% 1.94/1.31  Index Insertion      : 0.00
% 1.94/1.31  Index Deletion       : 0.00
% 1.94/1.31  Index Matching       : 0.00
% 1.94/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
