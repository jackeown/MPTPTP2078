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
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  68 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_68,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(c_28,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_113,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [B_18,A_17] : k5_relat_1(k6_relat_1(B_18),k6_relat_1(A_17)) = k6_relat_1(k3_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_120,plain,(
    ! [A_17,A_36] :
      ( k7_relat_1(k6_relat_1(A_17),A_36) = k6_relat_1(k3_xboole_0(A_17,A_36))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_32])).

tff(c_133,plain,(
    ! [A_38,A_39] : k7_relat_1(k6_relat_1(A_38),A_39) = k6_relat_1(k3_xboole_0(A_38,A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_139,plain,(
    ! [A_38,A_39] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_38,A_39))) = k9_relat_1(k6_relat_1(A_38),A_39)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_20])).

tff(c_145,plain,(
    ! [A_38,A_39] : k9_relat_1(k6_relat_1(A_38),A_39) = k3_xboole_0(A_38,A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_139])).

tff(c_34,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,(
    k3_xboole_0('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski('#skF_1'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_237,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_tarski('#skF_1'(A_54,B_55,C_56),A_54)
      | k3_xboole_0(B_55,C_56) = A_54
      | ~ r1_tarski(A_54,C_56)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_241,plain,(
    ! [B_4,C_5] :
      ( k3_xboole_0(B_4,C_5) = C_5
      | ~ r1_tarski(C_5,C_5)
      | ~ r1_tarski(C_5,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_237])).

tff(c_303,plain,(
    ! [B_59,C_60] :
      ( k3_xboole_0(B_59,C_60) = C_60
      | ~ r1_tarski(C_60,B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_241])).

tff(c_312,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_63,c_303])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.32  
% 2.30/1.33  tff(f_66, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.30/1.33  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.30/1.33  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.30/1.33  tff(f_68, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.30/1.33  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.30/1.33  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.30/1.33  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.30/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.33  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.30/1.33  tff(c_28, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.30/1.33  tff(c_24, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.33  tff(c_113, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.33  tff(c_32, plain, (![B_18, A_17]: (k5_relat_1(k6_relat_1(B_18), k6_relat_1(A_17))=k6_relat_1(k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.33  tff(c_120, plain, (![A_17, A_36]: (k7_relat_1(k6_relat_1(A_17), A_36)=k6_relat_1(k3_xboole_0(A_17, A_36)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_32])).
% 2.30/1.33  tff(c_133, plain, (![A_38, A_39]: (k7_relat_1(k6_relat_1(A_38), A_39)=k6_relat_1(k3_xboole_0(A_38, A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_120])).
% 2.30/1.33  tff(c_20, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.30/1.33  tff(c_139, plain, (![A_38, A_39]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_38, A_39)))=k9_relat_1(k6_relat_1(A_38), A_39) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_20])).
% 2.30/1.33  tff(c_145, plain, (![A_38, A_39]: (k9_relat_1(k6_relat_1(A_38), A_39)=k3_xboole_0(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_139])).
% 2.30/1.33  tff(c_34, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.33  tff(c_147, plain, (k3_xboole_0('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_34])).
% 2.30/1.33  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.33  tff(c_59, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.33  tff(c_63, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_59])).
% 2.30/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.33  tff(c_10, plain, (![A_3, B_4, C_5]: (r1_tarski('#skF_1'(A_3, B_4, C_5), C_5) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.33  tff(c_237, plain, (![A_54, B_55, C_56]: (~r1_tarski('#skF_1'(A_54, B_55, C_56), A_54) | k3_xboole_0(B_55, C_56)=A_54 | ~r1_tarski(A_54, C_56) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.33  tff(c_241, plain, (![B_4, C_5]: (k3_xboole_0(B_4, C_5)=C_5 | ~r1_tarski(C_5, C_5) | ~r1_tarski(C_5, B_4))), inference(resolution, [status(thm)], [c_10, c_237])).
% 2.30/1.33  tff(c_303, plain, (![B_59, C_60]: (k3_xboole_0(B_59, C_60)=C_60 | ~r1_tarski(C_60, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_241])).
% 2.30/1.33  tff(c_312, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_63, c_303])).
% 2.30/1.33  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_312])).
% 2.30/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.33  
% 2.30/1.33  Inference rules
% 2.30/1.33  ----------------------
% 2.30/1.33  #Ref     : 0
% 2.30/1.33  #Sup     : 65
% 2.30/1.33  #Fact    : 0
% 2.30/1.33  #Define  : 0
% 2.30/1.33  #Split   : 1
% 2.30/1.33  #Chain   : 0
% 2.30/1.33  #Close   : 0
% 2.30/1.33  
% 2.30/1.33  Ordering : KBO
% 2.30/1.33  
% 2.30/1.33  Simplification rules
% 2.30/1.33  ----------------------
% 2.30/1.33  #Subsume      : 0
% 2.30/1.33  #Demod        : 22
% 2.30/1.33  #Tautology    : 38
% 2.30/1.33  #SimpNegUnit  : 1
% 2.30/1.33  #BackRed      : 1
% 2.30/1.33  
% 2.30/1.33  #Partial instantiations: 0
% 2.30/1.33  #Strategies tried      : 1
% 2.30/1.33  
% 2.30/1.33  Timing (in seconds)
% 2.30/1.33  ----------------------
% 2.30/1.33  Preprocessing        : 0.30
% 2.30/1.33  Parsing              : 0.17
% 2.30/1.33  CNF conversion       : 0.02
% 2.30/1.33  Main loop            : 0.22
% 2.30/1.33  Inferencing          : 0.09
% 2.30/1.33  Reduction            : 0.06
% 2.30/1.33  Demodulation         : 0.05
% 2.30/1.33  BG Simplification    : 0.01
% 2.30/1.33  Subsumption          : 0.04
% 2.30/1.33  Abstraction          : 0.01
% 2.30/1.33  MUC search           : 0.00
% 2.30/1.33  Cooper               : 0.00
% 2.30/1.33  Total                : 0.54
% 2.30/1.33  Index Insertion      : 0.00
% 2.30/1.33  Index Deletion       : 0.00
% 2.30/1.33  Index Matching       : 0.00
% 2.30/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
