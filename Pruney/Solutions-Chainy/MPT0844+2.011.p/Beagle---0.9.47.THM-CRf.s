%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 103 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_80,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_84,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_8])).

tff(c_90,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_87])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_98,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_94])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,A_24)
      | ~ r1_xboole_0(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_25])).

tff(c_39,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_xboole_0(A_30,C_31)
      | ~ r1_xboole_0(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_34] :
      ( r1_xboole_0(A_34,'#skF_2')
      | ~ r1_tarski(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_34] :
      ( r1_xboole_0('#skF_2',A_34)
      | ~ r1_tarski(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_116,plain,(
    ! [A_49,B_50] :
      ( k7_relat_1(A_49,B_50) = k1_xboole_0
      | ~ r1_xboole_0(B_50,k1_relat_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,(
    ! [A_56] :
      ( k7_relat_1(A_56,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_56)
      | ~ r1_tarski(k1_relat_1(A_56),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_59,c_116])).

tff(c_160,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_157])).

tff(c_167,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_160])).

tff(c_189,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k5_relset_1(A_57,B_58,C_59,D_60) = k7_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_192,plain,(
    ! [D_60] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_60) = k7_relat_1('#skF_4',D_60) ),
    inference(resolution,[status(thm)],[c_24,c_189])).

tff(c_20,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_194,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_20])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.89/1.20  
% 1.89/1.20  %Foreground sorts:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Background operators:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Foreground operators:
% 1.89/1.20  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.89/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.20  
% 1.89/1.21  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 1.89/1.21  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.89/1.21  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.89/1.21  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.89/1.21  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.89/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.89/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.89/1.21  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 1.89/1.21  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.89/1.21  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.89/1.21  tff(c_34, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.21  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_34])).
% 1.89/1.21  tff(c_80, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.21  tff(c_84, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_80])).
% 1.89/1.21  tff(c_8, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.21  tff(c_87, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_8])).
% 1.89/1.21  tff(c_90, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_87])).
% 1.89/1.21  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.21  tff(c_94, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_90, c_10])).
% 1.89/1.21  tff(c_98, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_94])).
% 1.89/1.21  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.89/1.21  tff(c_25, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.21  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_25])).
% 1.89/1.21  tff(c_39, plain, (![A_30, C_31, B_32]: (r1_xboole_0(A_30, C_31) | ~r1_xboole_0(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.21  tff(c_53, plain, (![A_34]: (r1_xboole_0(A_34, '#skF_2') | ~r1_tarski(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_39])).
% 1.89/1.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.21  tff(c_59, plain, (![A_34]: (r1_xboole_0('#skF_2', A_34) | ~r1_tarski(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_2])).
% 1.89/1.21  tff(c_116, plain, (![A_49, B_50]: (k7_relat_1(A_49, B_50)=k1_xboole_0 | ~r1_xboole_0(B_50, k1_relat_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.21  tff(c_157, plain, (![A_56]: (k7_relat_1(A_56, '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_56) | ~r1_tarski(k1_relat_1(A_56), '#skF_3'))), inference(resolution, [status(thm)], [c_59, c_116])).
% 1.89/1.21  tff(c_160, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_157])).
% 1.89/1.21  tff(c_167, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_160])).
% 1.89/1.21  tff(c_189, plain, (![A_57, B_58, C_59, D_60]: (k5_relset_1(A_57, B_58, C_59, D_60)=k7_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.21  tff(c_192, plain, (![D_60]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_60)=k7_relat_1('#skF_4', D_60))), inference(resolution, [status(thm)], [c_24, c_189])).
% 1.89/1.21  tff(c_20, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.89/1.21  tff(c_194, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_192, c_20])).
% 1.89/1.21  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_194])).
% 1.89/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  Inference rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Ref     : 0
% 1.89/1.21  #Sup     : 41
% 1.89/1.21  #Fact    : 0
% 1.89/1.21  #Define  : 0
% 1.89/1.21  #Split   : 4
% 1.89/1.21  #Chain   : 0
% 1.89/1.21  #Close   : 0
% 1.89/1.21  
% 1.89/1.21  Ordering : KBO
% 1.89/1.21  
% 1.89/1.21  Simplification rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Subsume      : 4
% 1.89/1.21  #Demod        : 7
% 1.89/1.21  #Tautology    : 5
% 1.89/1.21  #SimpNegUnit  : 0
% 1.89/1.21  #BackRed      : 1
% 1.89/1.21  
% 1.89/1.21  #Partial instantiations: 0
% 1.89/1.21  #Strategies tried      : 1
% 1.89/1.21  
% 1.89/1.21  Timing (in seconds)
% 1.89/1.21  ----------------------
% 1.89/1.22  Preprocessing        : 0.28
% 1.89/1.22  Parsing              : 0.15
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.22  Main loop            : 0.18
% 1.89/1.22  Inferencing          : 0.07
% 1.89/1.22  Reduction            : 0.05
% 1.89/1.22  Demodulation         : 0.03
% 1.89/1.22  BG Simplification    : 0.01
% 1.89/1.22  Subsumption          : 0.05
% 1.89/1.22  Abstraction          : 0.01
% 1.89/1.22  MUC search           : 0.00
% 1.89/1.22  Cooper               : 0.00
% 1.89/1.22  Total                : 0.49
% 1.89/1.22  Index Insertion      : 0.00
% 1.89/1.22  Index Deletion       : 0.00
% 1.89/1.22  Index Matching       : 0.00
% 1.89/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
