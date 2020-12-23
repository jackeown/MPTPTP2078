%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:38 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 125 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_34,B_35,D_36] :
      ( r2_relset_1(A_34,B_35,D_36,D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_39,plain,(
    ! [C_31,A_32,B_33] :
      ( v4_relat_1(C_31,A_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_8])).

tff(c_49,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46])).

tff(c_58,plain,(
    ! [C_37,A_38,B_39] :
      ( k7_relat_1(k7_relat_1(C_37,A_38),B_39) = k7_relat_1(C_37,A_38)
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [B_39] :
      ( k7_relat_1('#skF_4',B_39) = k7_relat_1('#skF_4','#skF_2')
      | ~ r1_tarski('#skF_2',B_39)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_58])).

tff(c_82,plain,(
    ! [B_44] :
      ( k7_relat_1('#skF_4',B_44) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_49,c_73])).

tff(c_86,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_78,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k5_relset_1(A_40,B_41,C_42,D_43) = k7_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [D_43] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_43) = k7_relat_1('#skF_4',D_43) ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_20])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_86,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.89/1.23  
% 1.89/1.23  %Foreground sorts:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Background operators:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Foreground operators:
% 1.89/1.23  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.89/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.89/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.23  
% 1.89/1.24  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 1.89/1.24  tff(f_64, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.89/1.24  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.89/1.24  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.89/1.24  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.89/1.24  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.89/1.24  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.89/1.24  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.89/1.24  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_54, plain, (![A_34, B_35, D_36]: (r2_relset_1(A_34, B_35, D_36, D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.24  tff(c_57, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_54])).
% 1.89/1.24  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.24  tff(c_26, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.24  tff(c_29, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_26])).
% 1.89/1.24  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_29])).
% 1.89/1.24  tff(c_39, plain, (![C_31, A_32, B_33]: (v4_relat_1(C_31, A_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.24  tff(c_43, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_39])).
% 1.89/1.24  tff(c_8, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.89/1.24  tff(c_46, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_8])).
% 1.89/1.24  tff(c_49, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46])).
% 1.89/1.24  tff(c_58, plain, (![C_37, A_38, B_39]: (k7_relat_1(k7_relat_1(C_37, A_38), B_39)=k7_relat_1(C_37, A_38) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.24  tff(c_73, plain, (![B_39]: (k7_relat_1('#skF_4', B_39)=k7_relat_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_2', B_39) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_58])).
% 1.89/1.24  tff(c_82, plain, (![B_44]: (k7_relat_1('#skF_4', B_44)='#skF_4' | ~r1_tarski('#skF_2', B_44))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_49, c_73])).
% 1.89/1.24  tff(c_86, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_82])).
% 1.89/1.24  tff(c_78, plain, (![A_40, B_41, C_42, D_43]: (k5_relset_1(A_40, B_41, C_42, D_43)=k7_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.24  tff(c_81, plain, (![D_43]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_43)=k7_relat_1('#skF_4', D_43))), inference(resolution, [status(thm)], [c_24, c_78])).
% 1.89/1.24  tff(c_20, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.24  tff(c_97, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_20])).
% 1.89/1.24  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_86, c_97])).
% 1.89/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.24  
% 1.89/1.24  Inference rules
% 1.89/1.24  ----------------------
% 1.89/1.24  #Ref     : 0
% 1.89/1.24  #Sup     : 17
% 1.89/1.24  #Fact    : 0
% 1.89/1.24  #Define  : 0
% 1.89/1.24  #Split   : 0
% 1.89/1.24  #Chain   : 0
% 1.89/1.24  #Close   : 0
% 1.89/1.24  
% 1.89/1.24  Ordering : KBO
% 1.89/1.24  
% 1.89/1.24  Simplification rules
% 1.89/1.24  ----------------------
% 1.89/1.24  #Subsume      : 0
% 1.89/1.24  #Demod        : 9
% 1.89/1.24  #Tautology    : 6
% 1.89/1.24  #SimpNegUnit  : 0
% 1.89/1.24  #BackRed      : 1
% 1.89/1.24  
% 1.89/1.24  #Partial instantiations: 0
% 1.89/1.24  #Strategies tried      : 1
% 1.89/1.24  
% 1.89/1.24  Timing (in seconds)
% 1.89/1.24  ----------------------
% 1.89/1.25  Preprocessing        : 0.30
% 1.89/1.25  Parsing              : 0.16
% 1.89/1.25  CNF conversion       : 0.02
% 1.89/1.25  Main loop            : 0.11
% 1.89/1.25  Inferencing          : 0.04
% 1.89/1.25  Reduction            : 0.04
% 1.89/1.25  Demodulation         : 0.03
% 1.89/1.25  BG Simplification    : 0.01
% 1.89/1.25  Subsumption          : 0.01
% 1.89/1.25  Abstraction          : 0.01
% 1.89/1.25  MUC search           : 0.00
% 1.89/1.25  Cooper               : 0.00
% 1.89/1.25  Total                : 0.43
% 1.89/1.25  Index Insertion      : 0.00
% 1.89/1.25  Index Deletion       : 0.00
% 1.89/1.25  Index Matching       : 0.00
% 1.89/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
