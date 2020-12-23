%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.59s
% Verified   : 
% Statistics : Number of formulae       :   46 (  71 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 163 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k8_relat_1(A_11,B_12),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k8_relat_1(A_44,B_45),B_45) = B_45
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [A_44,B_45,C_3] :
      ( r1_tarski(k8_relat_1(A_44,B_45),C_3)
      | ~ r1_tarski(B_45,C_3)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(A_37)
      | ~ v1_relat_1(B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_89,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_74])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [B_14,A_13,C_15] :
      ( k8_relat_1(B_14,k8_relat_1(A_13,C_15)) = k8_relat_1(A_13,C_15)
      | ~ r1_tarski(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_154,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k8_relat_1(A_49,B_50),k8_relat_1(A_49,C_51))
      | ~ r1_tarski(B_50,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1634,plain,(
    ! [A_143,C_144,B_145,C_146] :
      ( r1_tarski(k8_relat_1(A_143,C_144),k8_relat_1(B_145,C_146))
      | ~ r1_tarski(k8_relat_1(A_143,C_144),C_146)
      | ~ v1_relat_1(C_146)
      | ~ v1_relat_1(k8_relat_1(A_143,C_144))
      | ~ r1_tarski(A_143,B_145)
      | ~ v1_relat_1(C_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_154])).

tff(c_18,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1658,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1634,c_18])).

tff(c_1692,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_24,c_1658])).

tff(c_1694,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1692])).

tff(c_1697,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_1694])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1697])).

tff(c_1702,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1692])).

tff(c_1772,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_1702])).

tff(c_1785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_1772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.35  
% 5.59/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.59/2.35  
% 5.59/2.35  %Foreground sorts:
% 5.59/2.35  
% 5.59/2.35  
% 5.59/2.35  %Background operators:
% 5.59/2.35  
% 5.59/2.35  
% 5.59/2.35  %Foreground operators:
% 5.59/2.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.59/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.59/2.35  tff('#skF_2', type, '#skF_2': $i).
% 5.59/2.35  tff('#skF_3', type, '#skF_3': $i).
% 5.59/2.35  tff('#skF_1', type, '#skF_1': $i).
% 5.59/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.59/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.59/2.35  tff('#skF_4', type, '#skF_4': $i).
% 5.59/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.59/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.59/2.35  
% 5.59/2.37  tff(f_75, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 5.59/2.37  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 5.59/2.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.59/2.37  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.59/2.37  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.59/2.37  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.59/2.37  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 5.59/2.37  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 5.59/2.37  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.59/2.37  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.59/2.37  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k8_relat_1(A_11, B_12), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.59/2.37  tff(c_29, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.59/2.37  tff(c_117, plain, (![A_44, B_45]: (k2_xboole_0(k8_relat_1(A_44, B_45), B_45)=B_45 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_12, c_29])).
% 5.59/2.37  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.59/2.37  tff(c_123, plain, (![A_44, B_45, C_3]: (r1_tarski(k8_relat_1(A_44, B_45), C_3) | ~r1_tarski(B_45, C_3) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_117, c_2])).
% 5.59/2.37  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.59/2.37  tff(c_69, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.59/2.37  tff(c_74, plain, (![A_37, B_38]: (v1_relat_1(A_37) | ~v1_relat_1(B_38) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_8, c_69])).
% 5.59/2.37  tff(c_89, plain, (![A_11, B_12]: (v1_relat_1(k8_relat_1(A_11, B_12)) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_12, c_74])).
% 5.59/2.37  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.59/2.37  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.59/2.37  tff(c_14, plain, (![B_14, A_13, C_15]: (k8_relat_1(B_14, k8_relat_1(A_13, C_15))=k8_relat_1(A_13, C_15) | ~r1_tarski(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.59/2.37  tff(c_154, plain, (![A_49, B_50, C_51]: (r1_tarski(k8_relat_1(A_49, B_50), k8_relat_1(A_49, C_51)) | ~r1_tarski(B_50, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.59/2.37  tff(c_1634, plain, (![A_143, C_144, B_145, C_146]: (r1_tarski(k8_relat_1(A_143, C_144), k8_relat_1(B_145, C_146)) | ~r1_tarski(k8_relat_1(A_143, C_144), C_146) | ~v1_relat_1(C_146) | ~v1_relat_1(k8_relat_1(A_143, C_144)) | ~r1_tarski(A_143, B_145) | ~v1_relat_1(C_144))), inference(superposition, [status(thm), theory('equality')], [c_14, c_154])).
% 5.59/2.37  tff(c_18, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.59/2.37  tff(c_1658, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1634, c_18])).
% 5.59/2.37  tff(c_1692, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_24, c_1658])).
% 5.59/2.37  tff(c_1694, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1692])).
% 5.59/2.37  tff(c_1697, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89, c_1694])).
% 5.59/2.37  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1697])).
% 5.59/2.37  tff(c_1702, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1692])).
% 5.59/2.37  tff(c_1772, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_1702])).
% 5.59/2.37  tff(c_1785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_1772])).
% 5.59/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.37  
% 5.59/2.37  Inference rules
% 5.59/2.37  ----------------------
% 5.59/2.37  #Ref     : 0
% 5.59/2.37  #Sup     : 468
% 5.59/2.37  #Fact    : 0
% 5.59/2.37  #Define  : 0
% 5.59/2.37  #Split   : 7
% 5.59/2.37  #Chain   : 0
% 5.59/2.37  #Close   : 0
% 5.59/2.37  
% 5.59/2.37  Ordering : KBO
% 5.59/2.37  
% 5.59/2.37  Simplification rules
% 5.59/2.37  ----------------------
% 5.59/2.37  #Subsume      : 132
% 5.59/2.37  #Demod        : 35
% 5.59/2.37  #Tautology    : 111
% 5.59/2.37  #SimpNegUnit  : 0
% 5.59/2.37  #BackRed      : 0
% 5.59/2.37  
% 5.59/2.37  #Partial instantiations: 0
% 5.59/2.37  #Strategies tried      : 1
% 5.59/2.37  
% 5.59/2.37  Timing (in seconds)
% 5.59/2.37  ----------------------
% 5.59/2.38  Preprocessing        : 0.45
% 5.59/2.38  Parsing              : 0.25
% 5.59/2.38  CNF conversion       : 0.03
% 5.59/2.38  Main loop            : 1.09
% 5.59/2.38  Inferencing          : 0.37
% 5.59/2.38  Reduction            : 0.25
% 5.59/2.38  Demodulation         : 0.17
% 5.59/2.38  BG Simplification    : 0.05
% 5.59/2.38  Subsumption          : 0.34
% 5.59/2.38  Abstraction          : 0.05
% 5.59/2.38  MUC search           : 0.00
% 5.59/2.38  Cooper               : 0.00
% 5.59/2.38  Total                : 1.58
% 5.59/2.38  Index Insertion      : 0.00
% 5.59/2.38  Index Deletion       : 0.00
% 5.59/2.38  Index Matching       : 0.00
% 5.59/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
