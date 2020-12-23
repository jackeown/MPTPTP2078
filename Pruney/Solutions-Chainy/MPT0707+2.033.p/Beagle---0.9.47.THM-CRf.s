%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  71 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_26,A_1] :
      ( r1_tarski(A_26,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_26,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_70,plain,(
    ! [A_28,A_29] :
      ( r1_tarski(A_28,A_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(A_29)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_66])).

tff(c_74,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_28,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [B_34,A_35] :
      ( k5_relat_1(B_34,k6_relat_1(A_35)) = B_34
      | ~ r1_tarski(k2_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [A_11,A_35] :
      ( k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_35)) = k6_relat_1(A_11)
      | ~ r1_tarski(A_11,A_35)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_93])).

tff(c_103,plain,(
    ! [A_38,A_39] :
      ( k5_relat_1(k6_relat_1(A_38),k6_relat_1(A_39)) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_99])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    ! [A_39,A_38] :
      ( k7_relat_1(k6_relat_1(A_39),A_38) = k6_relat_1(A_38)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_26])).

tff(c_123,plain,(
    ! [A_40,A_41] :
      ( k7_relat_1(k6_relat_1(A_40),A_41) = k6_relat_1(A_41)
      | ~ r1_tarski(A_41,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_109])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [A_40,A_41] :
      ( k9_relat_1(k6_relat_1(A_40),A_41) = k2_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_41,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_18])).

tff(c_137,plain,(
    ! [A_42,A_43] :
      ( k9_relat_1(k6_relat_1(A_42),A_43) = A_43
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_129])).

tff(c_32,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_143,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_32])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  
% 1.97/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.97/1.24  
% 1.97/1.24  %Foreground sorts:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Background operators:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Foreground operators:
% 1.97/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.97/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.24  
% 1.97/1.26  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.97/1.26  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.97/1.26  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.97/1.26  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.97/1.26  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.97/1.26  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.97/1.26  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.97/1.26  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.97/1.26  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.97/1.26  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.26  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.26  tff(c_62, plain, (![A_26, B_27]: (r2_hidden(A_26, B_27) | v1_xboole_0(B_27) | ~m1_subset_1(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.26  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.26  tff(c_66, plain, (![A_26, A_1]: (r1_tarski(A_26, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_26, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_62, c_2])).
% 1.97/1.26  tff(c_70, plain, (![A_28, A_29]: (r1_tarski(A_28, A_29) | ~m1_subset_1(A_28, k1_zfmisc_1(A_29)))), inference(negUnitSimplification, [status(thm)], [c_14, c_66])).
% 1.97/1.26  tff(c_74, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_70])).
% 1.97/1.26  tff(c_28, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.26  tff(c_22, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.26  tff(c_93, plain, (![B_34, A_35]: (k5_relat_1(B_34, k6_relat_1(A_35))=B_34 | ~r1_tarski(k2_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.26  tff(c_99, plain, (![A_11, A_35]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_35))=k6_relat_1(A_11) | ~r1_tarski(A_11, A_35) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_93])).
% 1.97/1.26  tff(c_103, plain, (![A_38, A_39]: (k5_relat_1(k6_relat_1(A_38), k6_relat_1(A_39))=k6_relat_1(A_38) | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_99])).
% 1.97/1.26  tff(c_26, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.26  tff(c_109, plain, (![A_39, A_38]: (k7_relat_1(k6_relat_1(A_39), A_38)=k6_relat_1(A_38) | ~v1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_38, A_39))), inference(superposition, [status(thm), theory('equality')], [c_103, c_26])).
% 1.97/1.26  tff(c_123, plain, (![A_40, A_41]: (k7_relat_1(k6_relat_1(A_40), A_41)=k6_relat_1(A_41) | ~r1_tarski(A_41, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_109])).
% 1.97/1.26  tff(c_18, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.97/1.26  tff(c_129, plain, (![A_40, A_41]: (k9_relat_1(k6_relat_1(A_40), A_41)=k2_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_41, A_40))), inference(superposition, [status(thm), theory('equality')], [c_123, c_18])).
% 1.97/1.26  tff(c_137, plain, (![A_42, A_43]: (k9_relat_1(k6_relat_1(A_42), A_43)=A_43 | ~r1_tarski(A_43, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_129])).
% 1.97/1.26  tff(c_32, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.26  tff(c_143, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_32])).
% 1.97/1.26  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_143])).
% 1.97/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  Inference rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Ref     : 0
% 1.97/1.26  #Sup     : 23
% 1.97/1.26  #Fact    : 0
% 1.97/1.26  #Define  : 0
% 1.97/1.26  #Split   : 0
% 1.97/1.26  #Chain   : 0
% 1.97/1.26  #Close   : 0
% 1.97/1.26  
% 1.97/1.26  Ordering : KBO
% 1.97/1.26  
% 1.97/1.26  Simplification rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Subsume      : 0
% 1.97/1.26  #Demod        : 6
% 1.97/1.26  #Tautology    : 14
% 1.97/1.26  #SimpNegUnit  : 1
% 1.97/1.26  #BackRed      : 0
% 1.97/1.26  
% 1.97/1.26  #Partial instantiations: 0
% 1.97/1.26  #Strategies tried      : 1
% 1.97/1.26  
% 1.97/1.26  Timing (in seconds)
% 1.97/1.26  ----------------------
% 1.97/1.26  Preprocessing        : 0.30
% 1.97/1.26  Parsing              : 0.17
% 1.97/1.26  CNF conversion       : 0.02
% 1.97/1.26  Main loop            : 0.14
% 1.97/1.26  Inferencing          : 0.06
% 1.97/1.26  Reduction            : 0.04
% 1.97/1.26  Demodulation         : 0.02
% 1.97/1.26  BG Simplification    : 0.01
% 1.97/1.26  Subsumption          : 0.02
% 1.97/1.26  Abstraction          : 0.01
% 1.97/1.26  MUC search           : 0.00
% 1.97/1.26  Cooper               : 0.00
% 1.97/1.26  Total                : 0.47
% 1.97/1.26  Index Insertion      : 0.00
% 1.97/1.26  Index Deletion       : 0.00
% 1.97/1.26  Index Matching       : 0.00
% 1.97/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
