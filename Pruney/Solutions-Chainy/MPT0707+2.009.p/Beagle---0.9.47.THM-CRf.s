%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:17 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   50 (  55 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  60 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( r1_tarski(C_9,A_5)
      | ~ r2_hidden(C_9,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,(
    ! [A_32,A_5] :
      ( r1_tarski(A_32,A_5)
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ m1_subset_1(A_32,k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_95,c_6])).

tff(c_103,plain,(
    ! [A_34,A_35] :
      ( r1_tarski(A_34,A_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(A_35)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_99])).

tff(c_107,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_relat_1(B_19),k6_relat_1(A_18)) = k6_relat_1(k3_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,(
    ! [B_38,A_39] :
      ( k9_relat_1(B_38,k2_relat_1(A_39)) = k2_relat_1(k5_relat_1(A_39,B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_134,plain,(
    ! [A_17,B_38] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_17),B_38)) = k9_relat_1(B_38,A_17)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_125])).

tff(c_139,plain,(
    ! [A_40,B_41] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_40),B_41)) = k9_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_134])).

tff(c_151,plain,(
    ! [A_18,B_19] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_18,B_19))) = k9_relat_1(k6_relat_1(A_18),B_19)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_139])).

tff(c_155,plain,(
    ! [A_18,B_19] : k9_relat_1(k6_relat_1(A_18),B_19) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_151])).

tff(c_32,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,(
    k3_xboole_0('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_32])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.91/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.20  
% 1.98/1.21  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.98/1.21  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.98/1.21  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.98/1.21  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.98/1.21  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.98/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.98/1.21  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.98/1.21  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.98/1.21  tff(f_62, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.98/1.21  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.98/1.21  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.98/1.21  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.21  tff(c_95, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.21  tff(c_6, plain, (![C_9, A_5]: (r1_tarski(C_9, A_5) | ~r2_hidden(C_9, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.21  tff(c_99, plain, (![A_32, A_5]: (r1_tarski(A_32, A_5) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~m1_subset_1(A_32, k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_95, c_6])).
% 1.98/1.21  tff(c_103, plain, (![A_34, A_35]: (r1_tarski(A_34, A_35) | ~m1_subset_1(A_34, k1_zfmisc_1(A_35)))), inference(negUnitSimplification, [status(thm)], [c_18, c_99])).
% 1.98/1.21  tff(c_107, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_103])).
% 1.98/1.21  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.21  tff(c_111, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_107, c_4])).
% 1.98/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.21  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.21  tff(c_28, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.21  tff(c_30, plain, (![B_19, A_18]: (k5_relat_1(k6_relat_1(B_19), k6_relat_1(A_18))=k6_relat_1(k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.21  tff(c_125, plain, (![B_38, A_39]: (k9_relat_1(B_38, k2_relat_1(A_39))=k2_relat_1(k5_relat_1(A_39, B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.21  tff(c_134, plain, (![A_17, B_38]: (k2_relat_1(k5_relat_1(k6_relat_1(A_17), B_38))=k9_relat_1(B_38, A_17) | ~v1_relat_1(B_38) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_125])).
% 1.98/1.21  tff(c_139, plain, (![A_40, B_41]: (k2_relat_1(k5_relat_1(k6_relat_1(A_40), B_41))=k9_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_134])).
% 1.98/1.21  tff(c_151, plain, (![A_18, B_19]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_18, B_19)))=k9_relat_1(k6_relat_1(A_18), B_19) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_139])).
% 1.98/1.21  tff(c_155, plain, (![A_18, B_19]: (k9_relat_1(k6_relat_1(A_18), B_19)=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28, c_151])).
% 1.98/1.21  tff(c_32, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.98/1.21  tff(c_156, plain, (k3_xboole_0('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_32])).
% 1.98/1.21  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_2, c_156])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 27
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 0
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 0
% 1.98/1.21  #Demod        : 6
% 1.98/1.21  #Tautology    : 21
% 1.98/1.21  #SimpNegUnit  : 1
% 1.98/1.21  #BackRed      : 1
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.22  Preprocessing        : 0.31
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.13
% 1.98/1.22  Inferencing          : 0.05
% 1.98/1.22  Reduction            : 0.04
% 1.98/1.22  Demodulation         : 0.03
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.02
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.46
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
