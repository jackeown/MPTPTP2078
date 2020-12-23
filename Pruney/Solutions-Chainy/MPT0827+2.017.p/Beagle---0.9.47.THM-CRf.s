%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:17 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 ( 130 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_51])).

tff(c_24,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k2_relat_1(A_43),k2_relat_1(B_44))
      | ~ r1_tarski(A_43,B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [A_9,B_44] :
      ( r1_tarski(A_9,k2_relat_1(B_44))
      | ~ r1_tarski(k6_relat_1(A_9),B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_122])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,k2_relat_1(B_46))
      | ~ r1_tarski(k6_relat_1(A_45),B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_125])).

tff(c_136,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_133])).

tff(c_139,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_136])).

tff(c_176,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_180,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_101,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_55])).

tff(c_10,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_relat_1(A_36),k1_relat_1(B_37))
      | ~ r1_tarski(A_36,B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    ! [A_9,B_37] :
      ( r1_tarski(A_9,k1_relat_1(B_37))
      | ~ r1_tarski(k6_relat_1(A_9),B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_111,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,k1_relat_1(B_42))
      | ~ r1_tarski(k6_relat_1(A_41),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_114,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_117,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_114])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_117])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_187,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_120])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:56:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.00/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.00/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.21  
% 2.13/1.22  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.13/1.22  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.13/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.13/1.22  tff(f_53, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.13/1.22  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.13/1.22  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.13/1.22  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.13/1.22  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.13/1.22  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.13/1.22  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.22  tff(c_48, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.22  tff(c_51, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_48])).
% 2.13/1.22  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_51])).
% 2.13/1.22  tff(c_24, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.22  tff(c_14, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.22  tff(c_12, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.22  tff(c_122, plain, (![A_43, B_44]: (r1_tarski(k2_relat_1(A_43), k2_relat_1(B_44)) | ~r1_tarski(A_43, B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.22  tff(c_125, plain, (![A_9, B_44]: (r1_tarski(A_9, k2_relat_1(B_44)) | ~r1_tarski(k6_relat_1(A_9), B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_122])).
% 2.13/1.22  tff(c_133, plain, (![A_45, B_46]: (r1_tarski(A_45, k2_relat_1(B_46)) | ~r1_tarski(k6_relat_1(A_45), B_46) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_125])).
% 2.13/1.22  tff(c_136, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_133])).
% 2.13/1.22  tff(c_139, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_136])).
% 2.13/1.22  tff(c_176, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.22  tff(c_180, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.13/1.22  tff(c_101, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.22  tff(c_105, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_101])).
% 2.13/1.22  tff(c_22, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.22  tff(c_55, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.13/1.22  tff(c_106, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_55])).
% 2.13/1.22  tff(c_10, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.22  tff(c_90, plain, (![A_36, B_37]: (r1_tarski(k1_relat_1(A_36), k1_relat_1(B_37)) | ~r1_tarski(A_36, B_37) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.22  tff(c_93, plain, (![A_9, B_37]: (r1_tarski(A_9, k1_relat_1(B_37)) | ~r1_tarski(k6_relat_1(A_9), B_37) | ~v1_relat_1(B_37) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.13/1.22  tff(c_111, plain, (![A_41, B_42]: (r1_tarski(A_41, k1_relat_1(B_42)) | ~r1_tarski(k6_relat_1(A_41), B_42) | ~v1_relat_1(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_93])).
% 2.13/1.22  tff(c_114, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_111])).
% 2.13/1.22  tff(c_117, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_114])).
% 2.13/1.22  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_117])).
% 2.13/1.22  tff(c_120, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_22])).
% 2.13/1.22  tff(c_187, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_120])).
% 2.13/1.22  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_187])).
% 2.13/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.22  
% 2.13/1.22  Inference rules
% 2.13/1.22  ----------------------
% 2.13/1.22  #Ref     : 0
% 2.13/1.22  #Sup     : 30
% 2.13/1.22  #Fact    : 0
% 2.13/1.22  #Define  : 0
% 2.13/1.22  #Split   : 1
% 2.13/1.22  #Chain   : 0
% 2.13/1.22  #Close   : 0
% 2.13/1.22  
% 2.13/1.22  Ordering : KBO
% 2.13/1.22  
% 2.13/1.22  Simplification rules
% 2.13/1.22  ----------------------
% 2.13/1.22  #Subsume      : 1
% 2.13/1.22  #Demod        : 21
% 2.13/1.22  #Tautology    : 11
% 2.13/1.22  #SimpNegUnit  : 1
% 2.13/1.22  #BackRed      : 3
% 2.13/1.22  
% 2.13/1.22  #Partial instantiations: 0
% 2.13/1.22  #Strategies tried      : 1
% 2.13/1.22  
% 2.13/1.22  Timing (in seconds)
% 2.13/1.22  ----------------------
% 2.13/1.23  Preprocessing        : 0.28
% 2.13/1.23  Parsing              : 0.15
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.23  Main loop            : 0.17
% 2.13/1.23  Inferencing          : 0.07
% 2.13/1.23  Reduction            : 0.06
% 2.13/1.23  Demodulation         : 0.04
% 2.13/1.23  BG Simplification    : 0.01
% 2.13/1.23  Subsumption          : 0.02
% 2.13/1.23  Abstraction          : 0.01
% 2.13/1.23  MUC search           : 0.00
% 2.13/1.23  Cooper               : 0.00
% 2.13/1.23  Total                : 0.48
% 2.13/1.23  Index Insertion      : 0.00
% 2.13/1.23  Index Deletion       : 0.00
% 2.13/1.23  Index Matching       : 0.00
% 2.13/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
