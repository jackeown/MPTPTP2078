%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:33 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 103 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_27,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_57,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r1_tarski(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_86,plain,(
    ! [B_50] :
      ( r1_tarski(k1_relat_1(B_50),'#skF_3')
      | ~ v4_relat_1(B_50,'#skF_2')
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_51] :
      ( v4_relat_1(B_51,'#skF_3')
      | ~ v4_relat_1(B_51,'#skF_2')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_97,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_94])).

tff(c_100,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_97])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_106,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_103])).

tff(c_72,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k5_relset_1(A_45,B_46,C_47,D_48) = k7_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [D_48] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_48) = k7_relat_1('#skF_4',D_48) ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_22])).

tff(c_107,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_76])).

tff(c_208,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( r2_relset_1(A_75,B_76,C_77,C_77)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_215,plain,(
    ! [C_79] :
      ( r2_relset_1('#skF_2','#skF_1',C_79,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_208])).

tff(c_220,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.47  
% 2.27/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.47  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.47  
% 2.27/1.47  %Foreground sorts:
% 2.27/1.47  
% 2.27/1.47  
% 2.27/1.47  %Background operators:
% 2.27/1.47  
% 2.27/1.47  
% 2.27/1.47  %Foreground operators:
% 2.27/1.47  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.27/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.47  
% 2.27/1.48  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.27/1.48  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.27/1.48  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.48  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.27/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.27/1.48  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.27/1.48  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.27/1.48  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.27/1.48  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.48  tff(c_27, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.27/1.48  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_27])).
% 2.27/1.48  tff(c_57, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.48  tff(c_61, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.27/1.48  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.48  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.48  tff(c_39, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.48  tff(c_46, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r1_tarski(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_39])).
% 2.27/1.48  tff(c_86, plain, (![B_50]: (r1_tarski(k1_relat_1(B_50), '#skF_3') | ~v4_relat_1(B_50, '#skF_2') | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.27/1.48  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.48  tff(c_94, plain, (![B_51]: (v4_relat_1(B_51, '#skF_3') | ~v4_relat_1(B_51, '#skF_2') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_86, c_4])).
% 2.27/1.48  tff(c_97, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_61, c_94])).
% 2.27/1.48  tff(c_100, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_97])).
% 2.27/1.48  tff(c_8, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.27/1.48  tff(c_103, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_8])).
% 2.27/1.48  tff(c_106, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_103])).
% 2.27/1.48  tff(c_72, plain, (![A_45, B_46, C_47, D_48]: (k5_relset_1(A_45, B_46, C_47, D_48)=k7_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.48  tff(c_75, plain, (![D_48]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_48)=k7_relat_1('#skF_4', D_48))), inference(resolution, [status(thm)], [c_26, c_72])).
% 2.27/1.48  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.27/1.48  tff(c_76, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_22])).
% 2.27/1.48  tff(c_107, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_76])).
% 2.27/1.48  tff(c_208, plain, (![A_75, B_76, C_77, D_78]: (r2_relset_1(A_75, B_76, C_77, C_77) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.48  tff(c_215, plain, (![C_79]: (r2_relset_1('#skF_2', '#skF_1', C_79, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_208])).
% 2.27/1.48  tff(c_220, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_215])).
% 2.27/1.48  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_220])).
% 2.27/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.48  
% 2.27/1.48  Inference rules
% 2.27/1.48  ----------------------
% 2.27/1.48  #Ref     : 0
% 2.27/1.48  #Sup     : 41
% 2.27/1.48  #Fact    : 0
% 2.27/1.48  #Define  : 0
% 2.27/1.48  #Split   : 0
% 2.27/1.48  #Chain   : 0
% 2.27/1.48  #Close   : 0
% 2.27/1.48  
% 2.27/1.48  Ordering : KBO
% 2.27/1.48  
% 2.27/1.48  Simplification rules
% 2.27/1.48  ----------------------
% 2.27/1.48  #Subsume      : 1
% 2.27/1.48  #Demod        : 18
% 2.27/1.48  #Tautology    : 15
% 2.27/1.48  #SimpNegUnit  : 2
% 2.27/1.48  #BackRed      : 2
% 2.27/1.48  
% 2.27/1.48  #Partial instantiations: 0
% 2.27/1.48  #Strategies tried      : 1
% 2.27/1.48  
% 2.27/1.48  Timing (in seconds)
% 2.27/1.48  ----------------------
% 2.27/1.48  Preprocessing        : 0.37
% 2.27/1.48  Parsing              : 0.22
% 2.27/1.48  CNF conversion       : 0.02
% 2.27/1.48  Main loop            : 0.18
% 2.27/1.48  Inferencing          : 0.07
% 2.27/1.49  Reduction            : 0.05
% 2.27/1.49  Demodulation         : 0.04
% 2.27/1.49  BG Simplification    : 0.01
% 2.27/1.49  Subsumption          : 0.03
% 2.27/1.49  Abstraction          : 0.01
% 2.27/1.49  MUC search           : 0.00
% 2.27/1.49  Cooper               : 0.00
% 2.27/1.49  Total                : 0.58
% 2.27/1.49  Index Insertion      : 0.00
% 2.27/1.49  Index Deletion       : 0.00
% 2.27/1.49  Index Matching       : 0.00
% 2.27/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
