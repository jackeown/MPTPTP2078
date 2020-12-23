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
% DateTime   : Thu Dec  3 10:07:07 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 120 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_14,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_29,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_32])).

tff(c_76,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    ! [C_33,A_34,B_35] :
      ( v4_relat_1(C_33,A_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_59,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_60,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = B_36
      | ~ v4_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_60])).

tff(c_66,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_63])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_18,A_17)),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_18])).

tff(c_74,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_70])).

tff(c_12,plain,(
    ! [A_12] :
      ( k2_xboole_0(k1_relat_1(A_12),k2_relat_1(A_12)) = k3_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    ! [A_43,C_44,B_45,D_46] :
      ( r1_tarski(k2_xboole_0(A_43,C_44),k2_xboole_0(B_45,D_46))
      | ~ r1_tarski(C_44,D_46)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_47,B_48,D_49] :
      ( r1_tarski(k3_relat_1(A_47),k2_xboole_0(B_48,D_49))
      | ~ r1_tarski(k2_relat_1(A_47),D_49)
      | ~ r1_tarski(k1_relat_1(A_47),B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_86])).

tff(c_24,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_96,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_24])).

tff(c_102,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_74,c_96])).

tff(c_105,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_80,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.13  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.71/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.71/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.71/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.13  
% 1.88/1.14  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.88/1.14  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 1.88/1.14  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.88/1.14  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.88/1.14  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.88/1.14  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.88/1.14  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.88/1.14  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.88/1.14  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 1.88/1.14  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.14  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.14  tff(c_29, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.14  tff(c_32, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_29])).
% 1.88/1.14  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_32])).
% 1.88/1.14  tff(c_76, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.14  tff(c_80, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_76])).
% 1.88/1.14  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.14  tff(c_55, plain, (![C_33, A_34, B_35]: (v4_relat_1(C_33, A_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.14  tff(c_59, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_55])).
% 1.88/1.14  tff(c_60, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=B_36 | ~v4_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.14  tff(c_63, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_59, c_60])).
% 1.88/1.14  tff(c_66, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_63])).
% 1.88/1.14  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(k7_relat_1(B_18, A_17)), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.88/1.14  tff(c_70, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_18])).
% 1.88/1.14  tff(c_74, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_70])).
% 1.88/1.14  tff(c_12, plain, (![A_12]: (k2_xboole_0(k1_relat_1(A_12), k2_relat_1(A_12))=k3_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.14  tff(c_86, plain, (![A_43, C_44, B_45, D_46]: (r1_tarski(k2_xboole_0(A_43, C_44), k2_xboole_0(B_45, D_46)) | ~r1_tarski(C_44, D_46) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.14  tff(c_93, plain, (![A_47, B_48, D_49]: (r1_tarski(k3_relat_1(A_47), k2_xboole_0(B_48, D_49)) | ~r1_tarski(k2_relat_1(A_47), D_49) | ~r1_tarski(k1_relat_1(A_47), B_48) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_86])).
% 1.88/1.14  tff(c_24, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.14  tff(c_96, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_24])).
% 1.88/1.14  tff(c_102, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_74, c_96])).
% 1.88/1.14  tff(c_105, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_102])).
% 1.88/1.14  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_80, c_105])).
% 1.88/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.14  
% 1.88/1.14  Inference rules
% 1.88/1.14  ----------------------
% 1.88/1.14  #Ref     : 0
% 1.88/1.14  #Sup     : 17
% 1.88/1.14  #Fact    : 0
% 1.88/1.14  #Define  : 0
% 1.88/1.14  #Split   : 0
% 1.88/1.14  #Chain   : 0
% 1.88/1.14  #Close   : 0
% 1.88/1.14  
% 1.88/1.14  Ordering : KBO
% 1.88/1.14  
% 1.88/1.14  Simplification rules
% 1.88/1.14  ----------------------
% 1.88/1.14  #Subsume      : 0
% 1.88/1.14  #Demod        : 7
% 1.88/1.14  #Tautology    : 7
% 1.88/1.14  #SimpNegUnit  : 0
% 1.88/1.14  #BackRed      : 0
% 1.88/1.14  
% 1.88/1.14  #Partial instantiations: 0
% 1.88/1.14  #Strategies tried      : 1
% 1.88/1.14  
% 1.88/1.14  Timing (in seconds)
% 1.88/1.14  ----------------------
% 1.88/1.15  Preprocessing        : 0.27
% 1.88/1.15  Parsing              : 0.16
% 1.88/1.15  CNF conversion       : 0.02
% 1.88/1.15  Main loop            : 0.12
% 1.88/1.15  Inferencing          : 0.06
% 1.88/1.15  Reduction            : 0.03
% 1.88/1.15  Demodulation         : 0.03
% 1.88/1.15  BG Simplification    : 0.01
% 1.88/1.15  Subsumption          : 0.01
% 1.88/1.15  Abstraction          : 0.00
% 1.88/1.15  MUC search           : 0.00
% 1.88/1.15  Cooper               : 0.00
% 1.88/1.15  Total                : 0.42
% 1.88/1.15  Index Insertion      : 0.00
% 1.88/1.15  Index Deletion       : 0.00
% 1.88/1.15  Index Matching       : 0.00
% 1.88/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
