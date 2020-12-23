%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:03 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 104 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 158 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_80,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_83])).

tff(c_188,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_192,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_188])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_167,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_171,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_167])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(B_33,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_8,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [B_33,A_32] : k2_xboole_0(B_33,A_32) = k2_xboole_0(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_8])).

tff(c_143,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,k2_xboole_0(C_37,B_38))
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_149,plain,(
    ! [A_36,B_33,A_32] :
      ( r1_tarski(A_36,k2_xboole_0(B_33,A_32))
      | ~ r1_tarski(A_36,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_143])).

tff(c_20,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_223,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(k2_xboole_0(A_57,C_58),B_59)
      | ~ r1_tarski(C_58,B_59)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_295,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k3_relat_1(A_76),B_77)
      | ~ r1_tarski(k2_relat_1(A_76),B_77)
      | ~ r1_tarski(k1_relat_1(A_76),B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_304,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_295,c_28])).

tff(c_313,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_304])).

tff(c_321,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_334,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_149,c_321])).

tff(c_338,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_171,c_338])).

tff(c_343,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_358,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_343])).

tff(c_361,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_192,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.32  
% 2.40/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.32  
% 2.40/1.32  %Foreground sorts:
% 2.40/1.32  
% 2.40/1.32  
% 2.40/1.32  %Background operators:
% 2.40/1.32  
% 2.40/1.32  
% 2.40/1.32  %Foreground operators:
% 2.40/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.32  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.40/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.40/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.40/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.40/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.32  
% 2.40/1.34  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.40/1.34  tff(f_75, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 2.40/1.34  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.40/1.34  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.40/1.34  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.40/1.34  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.40/1.34  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.40/1.34  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.40/1.34  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.40/1.34  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.40/1.34  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.40/1.34  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.34  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.40/1.34  tff(c_80, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.40/1.34  tff(c_83, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_80])).
% 2.40/1.34  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_83])).
% 2.40/1.34  tff(c_188, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.40/1.34  tff(c_192, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_188])).
% 2.40/1.34  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.34  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.34  tff(c_167, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.40/1.34  tff(c_171, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_167])).
% 2.40/1.34  tff(c_14, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.34  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.40/1.34  tff(c_65, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.34  tff(c_87, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(B_33, A_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 2.40/1.34  tff(c_8, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.34  tff(c_93, plain, (![B_33, A_32]: (k2_xboole_0(B_33, A_32)=k2_xboole_0(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_87, c_8])).
% 2.40/1.34  tff(c_143, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, k2_xboole_0(C_37, B_38)) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.34  tff(c_149, plain, (![A_36, B_33, A_32]: (r1_tarski(A_36, k2_xboole_0(B_33, A_32)) | ~r1_tarski(A_36, B_33))), inference(superposition, [status(thm), theory('equality')], [c_93, c_143])).
% 2.40/1.34  tff(c_20, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.40/1.34  tff(c_223, plain, (![A_57, C_58, B_59]: (r1_tarski(k2_xboole_0(A_57, C_58), B_59) | ~r1_tarski(C_58, B_59) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.34  tff(c_295, plain, (![A_76, B_77]: (r1_tarski(k3_relat_1(A_76), B_77) | ~r1_tarski(k2_relat_1(A_76), B_77) | ~r1_tarski(k1_relat_1(A_76), B_77) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_20, c_223])).
% 2.40/1.34  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.40/1.34  tff(c_304, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_295, c_28])).
% 2.40/1.34  tff(c_313, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_304])).
% 2.40/1.34  tff(c_321, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_313])).
% 2.40/1.34  tff(c_334, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_149, c_321])).
% 2.40/1.34  tff(c_338, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_334])).
% 2.40/1.34  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_171, c_338])).
% 2.40/1.34  tff(c_343, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_313])).
% 2.40/1.34  tff(c_358, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_343])).
% 2.40/1.34  tff(c_361, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_358])).
% 2.40/1.34  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_192, c_361])).
% 2.40/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  Inference rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Ref     : 0
% 2.40/1.34  #Sup     : 76
% 2.40/1.34  #Fact    : 0
% 2.40/1.34  #Define  : 0
% 2.40/1.34  #Split   : 2
% 2.40/1.34  #Chain   : 0
% 2.40/1.34  #Close   : 0
% 2.40/1.34  
% 2.40/1.34  Ordering : KBO
% 2.40/1.34  
% 2.40/1.34  Simplification rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Subsume      : 14
% 2.40/1.34  #Demod        : 14
% 2.40/1.34  #Tautology    : 27
% 2.40/1.34  #SimpNegUnit  : 0
% 2.40/1.34  #BackRed      : 0
% 2.40/1.34  
% 2.40/1.34  #Partial instantiations: 0
% 2.40/1.34  #Strategies tried      : 1
% 2.40/1.34  
% 2.40/1.34  Timing (in seconds)
% 2.40/1.34  ----------------------
% 2.40/1.35  Preprocessing        : 0.30
% 2.40/1.35  Parsing              : 0.17
% 2.40/1.35  CNF conversion       : 0.02
% 2.40/1.35  Main loop            : 0.27
% 2.40/1.35  Inferencing          : 0.10
% 2.40/1.35  Reduction            : 0.09
% 2.40/1.35  Demodulation         : 0.07
% 2.40/1.35  BG Simplification    : 0.01
% 2.40/1.35  Subsumption          : 0.05
% 2.40/1.35  Abstraction          : 0.01
% 2.40/1.35  MUC search           : 0.00
% 2.40/1.35  Cooper               : 0.00
% 2.40/1.35  Total                : 0.61
% 2.40/1.35  Index Insertion      : 0.00
% 2.40/1.35  Index Deletion       : 0.00
% 2.40/1.35  Index Matching       : 0.00
% 2.40/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
