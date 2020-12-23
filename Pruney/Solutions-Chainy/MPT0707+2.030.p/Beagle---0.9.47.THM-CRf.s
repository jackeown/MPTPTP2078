%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  71 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,A_30)
      | ~ m1_subset_1(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [B_29,A_1] :
      ( r1_tarski(B_29,A_1)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_83,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_79])).

tff(c_92,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_83])).

tff(c_24,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [B_41,A_42] :
      ( k5_relat_1(B_41,k6_relat_1(A_42)) = B_41
      | ~ r1_tarski(k2_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [A_12,A_42] :
      ( k5_relat_1(k6_relat_1(A_12),k6_relat_1(A_42)) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_42)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_131])).

tff(c_140,plain,(
    ! [A_43,A_44] :
      ( k5_relat_1(k6_relat_1(A_43),k6_relat_1(A_44)) = k6_relat_1(A_43)
      | ~ r1_tarski(A_43,A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_137])).

tff(c_34,plain,(
    ! [A_15,B_16] :
      ( k5_relat_1(k6_relat_1(A_15),B_16) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_146,plain,(
    ! [A_44,A_43] :
      ( k7_relat_1(k6_relat_1(A_44),A_43) = k6_relat_1(A_43)
      | ~ v1_relat_1(k6_relat_1(A_44))
      | ~ r1_tarski(A_43,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_34])).

tff(c_169,plain,(
    ! [A_47,A_48] :
      ( k7_relat_1(k6_relat_1(A_47),A_48) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_146])).

tff(c_26,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_175,plain,(
    ! [A_47,A_48] :
      ( k9_relat_1(k6_relat_1(A_47),A_48) = k2_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(k6_relat_1(A_47))
      | ~ r1_tarski(A_48,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_26])).

tff(c_183,plain,(
    ! [A_49,A_50] :
      ( k9_relat_1(k6_relat_1(A_49),A_50) = A_50
      | ~ r1_tarski(A_50,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30,c_175])).

tff(c_36,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_189,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_36])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:12:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.16  
% 1.88/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.88/1.16  
% 1.88/1.16  %Foreground sorts:
% 1.88/1.16  
% 1.88/1.16  
% 1.88/1.16  %Background operators:
% 1.88/1.16  
% 1.88/1.16  
% 1.88/1.16  %Foreground operators:
% 1.88/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.88/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.88/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.16  
% 1.88/1.17  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.88/1.17  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.88/1.17  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.88/1.17  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.88/1.17  tff(f_50, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.88/1.17  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.88/1.17  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.88/1.17  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.88/1.17  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.88/1.17  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.17  tff(c_22, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.17  tff(c_75, plain, (![B_29, A_30]: (r2_hidden(B_29, A_30) | ~m1_subset_1(B_29, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.17  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.17  tff(c_79, plain, (![B_29, A_1]: (r1_tarski(B_29, A_1) | ~m1_subset_1(B_29, k1_zfmisc_1(A_1)) | v1_xboole_0(k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_75, c_2])).
% 1.88/1.17  tff(c_83, plain, (![B_31, A_32]: (r1_tarski(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)))), inference(negUnitSimplification, [status(thm)], [c_22, c_79])).
% 1.88/1.17  tff(c_92, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_83])).
% 1.88/1.17  tff(c_24, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.17  tff(c_30, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.17  tff(c_131, plain, (![B_41, A_42]: (k5_relat_1(B_41, k6_relat_1(A_42))=B_41 | ~r1_tarski(k2_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.88/1.17  tff(c_137, plain, (![A_12, A_42]: (k5_relat_1(k6_relat_1(A_12), k6_relat_1(A_42))=k6_relat_1(A_12) | ~r1_tarski(A_12, A_42) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_131])).
% 1.88/1.17  tff(c_140, plain, (![A_43, A_44]: (k5_relat_1(k6_relat_1(A_43), k6_relat_1(A_44))=k6_relat_1(A_43) | ~r1_tarski(A_43, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_137])).
% 1.88/1.17  tff(c_34, plain, (![A_15, B_16]: (k5_relat_1(k6_relat_1(A_15), B_16)=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.88/1.17  tff(c_146, plain, (![A_44, A_43]: (k7_relat_1(k6_relat_1(A_44), A_43)=k6_relat_1(A_43) | ~v1_relat_1(k6_relat_1(A_44)) | ~r1_tarski(A_43, A_44))), inference(superposition, [status(thm), theory('equality')], [c_140, c_34])).
% 1.88/1.17  tff(c_169, plain, (![A_47, A_48]: (k7_relat_1(k6_relat_1(A_47), A_48)=k6_relat_1(A_48) | ~r1_tarski(A_48, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_146])).
% 1.88/1.17  tff(c_26, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.17  tff(c_175, plain, (![A_47, A_48]: (k9_relat_1(k6_relat_1(A_47), A_48)=k2_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(k6_relat_1(A_47)) | ~r1_tarski(A_48, A_47))), inference(superposition, [status(thm), theory('equality')], [c_169, c_26])).
% 1.88/1.17  tff(c_183, plain, (![A_49, A_50]: (k9_relat_1(k6_relat_1(A_49), A_50)=A_50 | ~r1_tarski(A_50, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30, c_175])).
% 1.88/1.17  tff(c_36, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.17  tff(c_189, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_36])).
% 1.88/1.17  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_189])).
% 1.88/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  Inference rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Ref     : 0
% 1.88/1.17  #Sup     : 32
% 1.88/1.17  #Fact    : 0
% 1.88/1.17  #Define  : 0
% 1.88/1.17  #Split   : 0
% 1.88/1.17  #Chain   : 0
% 1.88/1.17  #Close   : 0
% 1.88/1.17  
% 1.88/1.17  Ordering : KBO
% 1.88/1.17  
% 1.88/1.17  Simplification rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Subsume      : 3
% 1.88/1.17  #Demod        : 6
% 1.88/1.17  #Tautology    : 17
% 1.88/1.17  #SimpNegUnit  : 2
% 1.88/1.17  #BackRed      : 0
% 1.88/1.17  
% 1.88/1.17  #Partial instantiations: 0
% 1.88/1.17  #Strategies tried      : 1
% 1.88/1.17  
% 1.88/1.17  Timing (in seconds)
% 1.88/1.17  ----------------------
% 1.88/1.17  Preprocessing        : 0.27
% 1.88/1.17  Parsing              : 0.15
% 1.88/1.17  CNF conversion       : 0.02
% 1.88/1.17  Main loop            : 0.16
% 1.88/1.17  Inferencing          : 0.07
% 1.88/1.17  Reduction            : 0.04
% 1.88/1.17  Demodulation         : 0.03
% 1.88/1.17  BG Simplification    : 0.01
% 1.88/1.17  Subsumption          : 0.02
% 1.88/1.17  Abstraction          : 0.01
% 1.88/1.17  MUC search           : 0.00
% 1.88/1.17  Cooper               : 0.00
% 1.88/1.17  Total                : 0.46
% 1.88/1.17  Index Insertion      : 0.00
% 1.88/1.17  Index Deletion       : 0.00
% 1.88/1.17  Index Matching       : 0.00
% 1.88/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
