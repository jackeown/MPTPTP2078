%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:38 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   47 (  63 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  95 expanded)
%              Number of equality atoms :    9 (   9 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [A_35,B_36,D_37] :
      ( r2_relset_1(A_35,B_36,D_37,D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_39,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_58,plain,(
    ! [C_38,B_39,A_40] :
      ( v4_relat_1(C_38,B_39)
      | ~ v4_relat_1(C_38,A_40)
      | ~ v1_relat_1(C_38)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [B_39] :
      ( v4_relat_1('#skF_4',B_39)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_39) ) ),
    inference(resolution,[status(thm)],[c_43,c_58])).

tff(c_68,plain,(
    ! [B_45] :
      ( v4_relat_1('#skF_4',B_45)
      | ~ r1_tarski('#skF_2',B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [B_45] :
      ( k7_relat_1('#skF_4',B_45) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_45) ) ),
    inference(resolution,[status(thm)],[c_68,c_6])).

tff(c_80,plain,(
    ! [B_46] :
      ( k7_relat_1('#skF_4',B_46) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_84,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_64,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k5_relset_1(A_41,B_42,C_43,D_44) = k7_relat_1(C_43,D_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [D_44] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_44) = k7_relat_1('#skF_4',D_44) ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_20])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_84,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:50:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.21  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.21  
% 2.02/1.21  %Foreground sorts:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Background operators:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Foreground operators:
% 2.02/1.21  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.02/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.21  
% 2.02/1.22  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.02/1.22  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.02/1.22  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.02/1.22  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.02/1.22  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.02/1.22  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 2.02/1.22  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.02/1.22  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.02/1.22  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.22  tff(c_54, plain, (![A_35, B_36, D_37]: (r2_relset_1(A_35, B_36, D_37, D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.22  tff(c_57, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_54])).
% 2.02/1.22  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.22  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.22  tff(c_26, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.22  tff(c_29, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_26])).
% 2.02/1.22  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_29])).
% 2.02/1.22  tff(c_39, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.22  tff(c_43, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_39])).
% 2.02/1.22  tff(c_58, plain, (![C_38, B_39, A_40]: (v4_relat_1(C_38, B_39) | ~v4_relat_1(C_38, A_40) | ~v1_relat_1(C_38) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.22  tff(c_60, plain, (![B_39]: (v4_relat_1('#skF_4', B_39) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_39))), inference(resolution, [status(thm)], [c_43, c_58])).
% 2.02/1.22  tff(c_68, plain, (![B_45]: (v4_relat_1('#skF_4', B_45) | ~r1_tarski('#skF_2', B_45))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_60])).
% 2.02/1.22  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.22  tff(c_73, plain, (![B_45]: (k7_relat_1('#skF_4', B_45)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_45))), inference(resolution, [status(thm)], [c_68, c_6])).
% 2.02/1.22  tff(c_80, plain, (![B_46]: (k7_relat_1('#skF_4', B_46)='#skF_4' | ~r1_tarski('#skF_2', B_46))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_73])).
% 2.02/1.22  tff(c_84, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_80])).
% 2.02/1.22  tff(c_64, plain, (![A_41, B_42, C_43, D_44]: (k5_relset_1(A_41, B_42, C_43, D_44)=k7_relat_1(C_43, D_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.22  tff(c_67, plain, (![D_44]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_44)=k7_relat_1('#skF_4', D_44))), inference(resolution, [status(thm)], [c_24, c_64])).
% 2.02/1.22  tff(c_20, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.22  tff(c_89, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_20])).
% 2.02/1.22  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_84, c_89])).
% 2.02/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  Inference rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Ref     : 0
% 2.02/1.22  #Sup     : 14
% 2.02/1.22  #Fact    : 0
% 2.02/1.22  #Define  : 0
% 2.02/1.22  #Split   : 0
% 2.02/1.22  #Chain   : 0
% 2.02/1.22  #Close   : 0
% 2.02/1.22  
% 2.02/1.22  Ordering : KBO
% 2.02/1.22  
% 2.02/1.22  Simplification rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Subsume      : 0
% 2.02/1.22  #Demod        : 8
% 2.02/1.22  #Tautology    : 4
% 2.02/1.22  #SimpNegUnit  : 0
% 2.02/1.22  #BackRed      : 1
% 2.02/1.22  
% 2.02/1.22  #Partial instantiations: 0
% 2.02/1.22  #Strategies tried      : 1
% 2.02/1.22  
% 2.02/1.22  Timing (in seconds)
% 2.02/1.22  ----------------------
% 2.02/1.22  Preprocessing        : 0.32
% 2.02/1.22  Parsing              : 0.18
% 2.02/1.22  CNF conversion       : 0.02
% 2.02/1.22  Main loop            : 0.11
% 2.02/1.22  Inferencing          : 0.04
% 2.02/1.22  Reduction            : 0.03
% 2.02/1.22  Demodulation         : 0.03
% 2.02/1.23  BG Simplification    : 0.01
% 2.02/1.23  Subsumption          : 0.01
% 2.02/1.23  Abstraction          : 0.01
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.45
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.23  Index Deletion       : 0.00
% 2.02/1.23  Index Matching       : 0.00
% 2.02/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
