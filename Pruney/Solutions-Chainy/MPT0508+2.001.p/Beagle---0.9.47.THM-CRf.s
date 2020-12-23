%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   47 (  71 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 163 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_45,plain,(
    ! [B_25,A_26] :
      ( r1_tarski(k7_relat_1(B_25,A_26),B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    ! [B_44,A_45] :
      ( k2_xboole_0(k7_relat_1(B_44,A_45),B_44) = B_44
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [B_44,A_45,C_3] :
      ( r1_tarski(k7_relat_1(B_44,A_45),C_3)
      | ~ r1_tarski(B_44,C_3)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_2])).

tff(c_16,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

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
    ! [B_19,A_18] :
      ( v1_relat_1(k7_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_13,A_11),B_12) = k7_relat_1(C_13,A_11)
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_154,plain,(
    ! [B_49,A_50,C_51] :
      ( r1_tarski(k7_relat_1(B_49,A_50),k7_relat_1(C_51,A_50))
      | ~ r1_tarski(B_49,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1634,plain,(
    ! [C_143,A_144,C_145,B_146] :
      ( r1_tarski(k7_relat_1(C_143,A_144),k7_relat_1(C_145,B_146))
      | ~ r1_tarski(k7_relat_1(C_143,A_144),C_145)
      | ~ v1_relat_1(C_145)
      | ~ v1_relat_1(k7_relat_1(C_143,A_144))
      | ~ r1_tarski(A_144,B_146)
      | ~ v1_relat_1(C_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_154])).

tff(c_18,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1658,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1634,c_18])).

tff(c_1692,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_24,c_1658])).

tff(c_1694,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1692])).

tff(c_1697,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_1694])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1697])).

tff(c_1702,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4') ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.73  
% 3.90/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.73  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.90/1.73  
% 3.90/1.73  %Foreground sorts:
% 3.90/1.73  
% 3.90/1.73  
% 3.90/1.73  %Background operators:
% 3.90/1.73  
% 3.90/1.73  
% 3.90/1.73  %Foreground operators:
% 3.90/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.90/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.73  
% 3.90/1.74  tff(f_75, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 3.90/1.74  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.90/1.74  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.90/1.74  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.90/1.74  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.90/1.74  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.90/1.74  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 3.90/1.74  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 3.90/1.74  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.74  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.74  tff(c_45, plain, (![B_25, A_26]: (r1_tarski(k7_relat_1(B_25, A_26), B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.90/1.74  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.74  tff(c_117, plain, (![B_44, A_45]: (k2_xboole_0(k7_relat_1(B_44, A_45), B_44)=B_44 | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_45, c_4])).
% 3.90/1.74  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.74  tff(c_123, plain, (![B_44, A_45, C_3]: (r1_tarski(k7_relat_1(B_44, A_45), C_3) | ~r1_tarski(B_44, C_3) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_117, c_2])).
% 3.90/1.74  tff(c_16, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.90/1.74  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.90/1.74  tff(c_69, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.90/1.74  tff(c_74, plain, (![A_37, B_38]: (v1_relat_1(A_37) | ~v1_relat_1(B_38) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_8, c_69])).
% 3.90/1.74  tff(c_89, plain, (![B_19, A_18]: (v1_relat_1(k7_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_16, c_74])).
% 3.90/1.74  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.74  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.74  tff(c_12, plain, (![C_13, A_11, B_12]: (k7_relat_1(k7_relat_1(C_13, A_11), B_12)=k7_relat_1(C_13, A_11) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.90/1.74  tff(c_154, plain, (![B_49, A_50, C_51]: (r1_tarski(k7_relat_1(B_49, A_50), k7_relat_1(C_51, A_50)) | ~r1_tarski(B_49, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.90/1.74  tff(c_1634, plain, (![C_143, A_144, C_145, B_146]: (r1_tarski(k7_relat_1(C_143, A_144), k7_relat_1(C_145, B_146)) | ~r1_tarski(k7_relat_1(C_143, A_144), C_145) | ~v1_relat_1(C_145) | ~v1_relat_1(k7_relat_1(C_143, A_144)) | ~r1_tarski(A_144, B_146) | ~v1_relat_1(C_143))), inference(superposition, [status(thm), theory('equality')], [c_12, c_154])).
% 3.90/1.74  tff(c_18, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.74  tff(c_1658, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1634, c_18])).
% 3.90/1.74  tff(c_1692, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_24, c_1658])).
% 3.90/1.74  tff(c_1694, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1692])).
% 3.90/1.74  tff(c_1697, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89, c_1694])).
% 3.90/1.74  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1697])).
% 3.90/1.74  tff(c_1702, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_1692])).
% 3.90/1.74  tff(c_1772, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_1702])).
% 3.90/1.74  tff(c_1785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_1772])).
% 3.90/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.74  
% 3.90/1.74  Inference rules
% 3.90/1.74  ----------------------
% 3.90/1.74  #Ref     : 0
% 3.90/1.74  #Sup     : 468
% 3.90/1.74  #Fact    : 0
% 3.90/1.74  #Define  : 0
% 3.90/1.74  #Split   : 7
% 3.90/1.74  #Chain   : 0
% 3.90/1.74  #Close   : 0
% 3.90/1.74  
% 3.90/1.74  Ordering : KBO
% 3.90/1.74  
% 3.90/1.74  Simplification rules
% 3.90/1.74  ----------------------
% 3.90/1.74  #Subsume      : 132
% 3.90/1.74  #Demod        : 35
% 3.90/1.74  #Tautology    : 111
% 3.90/1.74  #SimpNegUnit  : 0
% 3.90/1.74  #BackRed      : 0
% 3.90/1.74  
% 3.90/1.74  #Partial instantiations: 0
% 3.90/1.74  #Strategies tried      : 1
% 3.90/1.74  
% 3.90/1.74  Timing (in seconds)
% 3.90/1.74  ----------------------
% 3.90/1.75  Preprocessing        : 0.28
% 3.90/1.75  Parsing              : 0.17
% 3.90/1.75  CNF conversion       : 0.02
% 3.90/1.75  Main loop            : 0.64
% 3.90/1.75  Inferencing          : 0.22
% 3.90/1.75  Reduction            : 0.14
% 3.90/1.75  Demodulation         : 0.10
% 3.90/1.75  BG Simplification    : 0.03
% 4.19/1.75  Subsumption          : 0.20
% 4.19/1.75  Abstraction          : 0.03
% 4.19/1.75  MUC search           : 0.00
% 4.19/1.75  Cooper               : 0.00
% 4.19/1.75  Total                : 0.95
% 4.19/1.75  Index Insertion      : 0.00
% 4.19/1.75  Index Deletion       : 0.00
% 4.19/1.75  Index Matching       : 0.00
% 4.19/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
