%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:19 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 118 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( k7_relat_1(B,A) = k7_relat_1(C,A)
           => k9_relat_1(B,A) = k9_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_57,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_24,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    ! [B_32,A_33] :
      ( k5_relat_1(B_32,k6_relat_1(A_33)) = B_32
      | ~ r1_tarski(k2_relat_1(B_32),A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [A_10,A_33] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_33)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_33)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_109])).

tff(c_180,plain,(
    ! [A_40,A_41] :
      ( k5_relat_1(k6_relat_1(A_40),k6_relat_1(A_41)) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_112])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_194,plain,(
    ! [A_41,A_40] :
      ( k7_relat_1(k6_relat_1(A_41),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ r1_tarski(A_40,A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_22])).

tff(c_217,plain,(
    ! [A_41,A_40] :
      ( k7_relat_1(k6_relat_1(A_41),A_40) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [B_34] :
      ( k5_relat_1(B_34,k6_relat_1(k2_relat_1(B_34))) = B_34
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_127,plain,(
    ! [A_13] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_13))),A_13) = k6_relat_1(A_13)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_13))))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_22])).

tff(c_140,plain,(
    ! [A_13] : k7_relat_1(k6_relat_1(A_13),A_13) = k6_relat_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_18,c_127])).

tff(c_146,plain,(
    ! [C_35,A_36,B_37] :
      ( k9_relat_1(C_35,A_36) = k9_relat_1(B_37,A_36)
      | k7_relat_1(C_35,A_36) != k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_249,plain,(
    ! [A_44,A_45,B_46] :
      ( k9_relat_1(k6_relat_1(A_44),A_45) = k9_relat_1(B_46,A_45)
      | k7_relat_1(k6_relat_1(A_44),A_45) != k7_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_253,plain,(
    ! [A_49,A_48,A_47] :
      ( k9_relat_1(k6_relat_1(A_49),A_48) = k9_relat_1(k6_relat_1(A_47),A_48)
      | k7_relat_1(k6_relat_1(A_49),A_48) != k7_relat_1(k6_relat_1(A_47),A_48) ) ),
    inference(resolution,[status(thm)],[c_24,c_249])).

tff(c_16,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_26] :
      ( k9_relat_1(A_26,k1_relat_1(A_26)) = k2_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_10] :
      ( k9_relat_1(k6_relat_1(A_10),A_10) = k2_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_66])).

tff(c_79,plain,(
    ! [A_10] : k9_relat_1(k6_relat_1(A_10),A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_75])).

tff(c_269,plain,(
    ! [A_49,A_48] :
      ( k9_relat_1(k6_relat_1(A_49),A_48) = A_48
      | k7_relat_1(k6_relat_1(A_49),A_48) != k7_relat_1(k6_relat_1(A_48),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_79])).

tff(c_326,plain,(
    ! [A_50,A_51] :
      ( k9_relat_1(k6_relat_1(A_50),A_51) = A_51
      | k7_relat_1(k6_relat_1(A_50),A_51) != k6_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_269])).

tff(c_30,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_369,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_30])).

tff(c_378,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_369])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.36  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.23/1.36  
% 2.23/1.36  %Foreground sorts:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Background operators:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Foreground operators:
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.36  
% 2.33/1.37  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.33/1.37  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.37  tff(f_68, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.33/1.37  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.33/1.37  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.33/1.37  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.33/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.37  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k7_relat_1(B, A) = k7_relat_1(C, A)) => (k9_relat_1(B, A) = k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_relat_1)).
% 2.33/1.37  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.33/1.37  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.37  tff(c_57, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.37  tff(c_65, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_57])).
% 2.33/1.37  tff(c_24, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.33/1.37  tff(c_18, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.37  tff(c_109, plain, (![B_32, A_33]: (k5_relat_1(B_32, k6_relat_1(A_33))=B_32 | ~r1_tarski(k2_relat_1(B_32), A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.37  tff(c_112, plain, (![A_10, A_33]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_33))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_33) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_109])).
% 2.33/1.37  tff(c_180, plain, (![A_40, A_41]: (k5_relat_1(k6_relat_1(A_40), k6_relat_1(A_41))=k6_relat_1(A_40) | ~r1_tarski(A_40, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_112])).
% 2.33/1.37  tff(c_22, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.37  tff(c_194, plain, (![A_41, A_40]: (k7_relat_1(k6_relat_1(A_41), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_41)) | ~r1_tarski(A_40, A_41))), inference(superposition, [status(thm), theory('equality')], [c_180, c_22])).
% 2.33/1.37  tff(c_217, plain, (![A_41, A_40]: (k7_relat_1(k6_relat_1(A_41), A_40)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 2.33/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.37  tff(c_120, plain, (![B_34]: (k5_relat_1(B_34, k6_relat_1(k2_relat_1(B_34)))=B_34 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_6, c_109])).
% 2.33/1.37  tff(c_127, plain, (![A_13]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_13))), A_13)=k6_relat_1(A_13) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_13)))) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_22])).
% 2.33/1.37  tff(c_140, plain, (![A_13]: (k7_relat_1(k6_relat_1(A_13), A_13)=k6_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_18, c_127])).
% 2.33/1.37  tff(c_146, plain, (![C_35, A_36, B_37]: (k9_relat_1(C_35, A_36)=k9_relat_1(B_37, A_36) | k7_relat_1(C_35, A_36)!=k7_relat_1(B_37, A_36) | ~v1_relat_1(C_35) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.33/1.37  tff(c_249, plain, (![A_44, A_45, B_46]: (k9_relat_1(k6_relat_1(A_44), A_45)=k9_relat_1(B_46, A_45) | k7_relat_1(k6_relat_1(A_44), A_45)!=k7_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_24, c_146])).
% 2.33/1.37  tff(c_253, plain, (![A_49, A_48, A_47]: (k9_relat_1(k6_relat_1(A_49), A_48)=k9_relat_1(k6_relat_1(A_47), A_48) | k7_relat_1(k6_relat_1(A_49), A_48)!=k7_relat_1(k6_relat_1(A_47), A_48))), inference(resolution, [status(thm)], [c_24, c_249])).
% 2.33/1.37  tff(c_16, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.37  tff(c_66, plain, (![A_26]: (k9_relat_1(A_26, k1_relat_1(A_26))=k2_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.37  tff(c_75, plain, (![A_10]: (k9_relat_1(k6_relat_1(A_10), A_10)=k2_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_66])).
% 2.33/1.37  tff(c_79, plain, (![A_10]: (k9_relat_1(k6_relat_1(A_10), A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_75])).
% 2.33/1.37  tff(c_269, plain, (![A_49, A_48]: (k9_relat_1(k6_relat_1(A_49), A_48)=A_48 | k7_relat_1(k6_relat_1(A_49), A_48)!=k7_relat_1(k6_relat_1(A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_253, c_79])).
% 2.33/1.37  tff(c_326, plain, (![A_50, A_51]: (k9_relat_1(k6_relat_1(A_50), A_51)=A_51 | k7_relat_1(k6_relat_1(A_50), A_51)!=k6_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_269])).
% 2.33/1.37  tff(c_30, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.37  tff(c_369, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_326, c_30])).
% 2.33/1.37  tff(c_378, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_217, c_369])).
% 2.33/1.37  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_378])).
% 2.33/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.37  
% 2.33/1.37  Inference rules
% 2.33/1.37  ----------------------
% 2.33/1.37  #Ref     : 0
% 2.33/1.37  #Sup     : 72
% 2.33/1.37  #Fact    : 0
% 2.33/1.37  #Define  : 0
% 2.33/1.37  #Split   : 1
% 2.33/1.37  #Chain   : 0
% 2.33/1.37  #Close   : 0
% 2.33/1.37  
% 2.33/1.37  Ordering : KBO
% 2.33/1.37  
% 2.33/1.37  Simplification rules
% 2.33/1.37  ----------------------
% 2.33/1.37  #Subsume      : 1
% 2.33/1.37  #Demod        : 72
% 2.33/1.37  #Tautology    : 38
% 2.33/1.37  #SimpNegUnit  : 0
% 2.33/1.37  #BackRed      : 0
% 2.33/1.37  
% 2.33/1.37  #Partial instantiations: 0
% 2.33/1.37  #Strategies tried      : 1
% 2.33/1.37  
% 2.33/1.37  Timing (in seconds)
% 2.33/1.37  ----------------------
% 2.33/1.37  Preprocessing        : 0.30
% 2.33/1.37  Parsing              : 0.17
% 2.33/1.37  CNF conversion       : 0.02
% 2.33/1.37  Main loop            : 0.23
% 2.33/1.37  Inferencing          : 0.09
% 2.33/1.37  Reduction            : 0.07
% 2.33/1.37  Demodulation         : 0.05
% 2.33/1.37  BG Simplification    : 0.01
% 2.33/1.38  Subsumption          : 0.04
% 2.33/1.38  Abstraction          : 0.01
% 2.33/1.38  MUC search           : 0.00
% 2.33/1.38  Cooper               : 0.00
% 2.33/1.38  Total                : 0.55
% 2.33/1.38  Index Insertion      : 0.00
% 2.33/1.38  Index Deletion       : 0.00
% 2.33/1.38  Index Matching       : 0.00
% 2.33/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
