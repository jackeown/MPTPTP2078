%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:19 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  66 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,negated_conjecture,(
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

tff(c_20,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [B_18,A_17] : k5_relat_1(k6_relat_1(B_18),k6_relat_1(A_17)) = k6_relat_1(k3_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117,plain,(
    ! [A_17,A_35] :
      ( k7_relat_1(k6_relat_1(A_17),A_35) = k6_relat_1(k3_xboole_0(A_17,A_35))
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_30])).

tff(c_130,plain,(
    ! [A_37,A_38] : k7_relat_1(k6_relat_1(A_37),A_38) = k6_relat_1(k3_xboole_0(A_37,A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_117])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_136,plain,(
    ! [A_37,A_38] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_37,A_38))) = k9_relat_1(k6_relat_1(A_37),A_38)
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_142,plain,(
    ! [A_37,A_38] : k9_relat_1(k6_relat_1(A_37),A_38) = k3_xboole_0(A_37,A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_136])).

tff(c_32,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_144,plain,(
    k3_xboole_0('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_56])).

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

tff(c_234,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_tarski('#skF_1'(A_53,B_54,C_55),A_53)
      | k3_xboole_0(B_54,C_55) = A_53
      | ~ r1_tarski(A_53,C_55)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_242,plain,(
    ! [B_4,C_5] :
      ( k3_xboole_0(B_4,C_5) = C_5
      | ~ r1_tarski(C_5,C_5)
      | ~ r1_tarski(C_5,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_234])).

tff(c_293,plain,(
    ! [B_59,C_60] :
      ( k3_xboole_0(B_59,C_60) = C_60
      | ~ r1_tarski(C_60,B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_242])).

tff(c_302,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_60,c_293])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 2.28/1.35  
% 2.28/1.35  %Foreground sorts:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Background operators:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Foreground operators:
% 2.28/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.28/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.35  
% 2.28/1.36  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.28/1.36  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.28/1.36  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.28/1.36  tff(f_66, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.28/1.36  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.28/1.36  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.28/1.36  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.36  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.28/1.36  tff(c_20, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.36  tff(c_26, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.36  tff(c_110, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.28/1.36  tff(c_30, plain, (![B_18, A_17]: (k5_relat_1(k6_relat_1(B_18), k6_relat_1(A_17))=k6_relat_1(k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.36  tff(c_117, plain, (![A_17, A_35]: (k7_relat_1(k6_relat_1(A_17), A_35)=k6_relat_1(k3_xboole_0(A_17, A_35)) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_30])).
% 2.28/1.36  tff(c_130, plain, (![A_37, A_38]: (k7_relat_1(k6_relat_1(A_37), A_38)=k6_relat_1(k3_xboole_0(A_37, A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_117])).
% 2.28/1.36  tff(c_22, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.36  tff(c_136, plain, (![A_37, A_38]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_37, A_38)))=k9_relat_1(k6_relat_1(A_37), A_38) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_22])).
% 2.28/1.36  tff(c_142, plain, (![A_37, A_38]: (k9_relat_1(k6_relat_1(A_37), A_38)=k3_xboole_0(A_37, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_136])).
% 2.28/1.36  tff(c_32, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.36  tff(c_144, plain, (k3_xboole_0('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_32])).
% 2.28/1.36  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.36  tff(c_56, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.36  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_56])).
% 2.28/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.36  tff(c_10, plain, (![A_3, B_4, C_5]: (r1_tarski('#skF_1'(A_3, B_4, C_5), C_5) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.36  tff(c_234, plain, (![A_53, B_54, C_55]: (~r1_tarski('#skF_1'(A_53, B_54, C_55), A_53) | k3_xboole_0(B_54, C_55)=A_53 | ~r1_tarski(A_53, C_55) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.36  tff(c_242, plain, (![B_4, C_5]: (k3_xboole_0(B_4, C_5)=C_5 | ~r1_tarski(C_5, C_5) | ~r1_tarski(C_5, B_4))), inference(resolution, [status(thm)], [c_10, c_234])).
% 2.28/1.36  tff(c_293, plain, (![B_59, C_60]: (k3_xboole_0(B_59, C_60)=C_60 | ~r1_tarski(C_60, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_242])).
% 2.28/1.36  tff(c_302, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_60, c_293])).
% 2.28/1.36  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_302])).
% 2.28/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.36  
% 2.28/1.36  Inference rules
% 2.28/1.36  ----------------------
% 2.28/1.36  #Ref     : 0
% 2.28/1.36  #Sup     : 63
% 2.28/1.36  #Fact    : 0
% 2.28/1.36  #Define  : 0
% 2.28/1.36  #Split   : 1
% 2.28/1.36  #Chain   : 0
% 2.28/1.36  #Close   : 0
% 2.28/1.36  
% 2.28/1.36  Ordering : KBO
% 2.28/1.36  
% 2.28/1.36  Simplification rules
% 2.28/1.36  ----------------------
% 2.28/1.36  #Subsume      : 0
% 2.28/1.36  #Demod        : 18
% 2.28/1.36  #Tautology    : 36
% 2.28/1.36  #SimpNegUnit  : 1
% 2.28/1.36  #BackRed      : 1
% 2.28/1.36  
% 2.28/1.36  #Partial instantiations: 0
% 2.28/1.36  #Strategies tried      : 1
% 2.28/1.36  
% 2.28/1.36  Timing (in seconds)
% 2.28/1.36  ----------------------
% 2.28/1.37  Preprocessing        : 0.36
% 2.28/1.37  Parsing              : 0.20
% 2.28/1.37  CNF conversion       : 0.02
% 2.28/1.37  Main loop            : 0.23
% 2.28/1.37  Inferencing          : 0.09
% 2.28/1.37  Reduction            : 0.06
% 2.28/1.37  Demodulation         : 0.05
% 2.28/1.37  BG Simplification    : 0.02
% 2.28/1.37  Subsumption          : 0.05
% 2.28/1.37  Abstraction          : 0.01
% 2.28/1.37  MUC search           : 0.00
% 2.28/1.37  Cooper               : 0.00
% 2.28/1.37  Total                : 0.62
% 2.28/1.37  Index Insertion      : 0.00
% 2.28/1.37  Index Deletion       : 0.00
% 2.28/1.37  Index Matching       : 0.00
% 2.28/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
