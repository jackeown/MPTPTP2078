%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:33 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 154 expanded)
%              Number of equality atoms :   20 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_40,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_18])).

tff(c_20,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_20])).

tff(c_22,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_108,plain,(
    ! [A_38,B_39] :
      ( k5_setfam_1(A_38,B_39) = k3_tarski(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_38] : k5_setfam_1(A_38,'#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_108])).

tff(c_136,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k5_setfam_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_149,plain,(
    ! [A_38] :
      ( m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1(A_38))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_136])).

tff(c_159,plain,(
    ! [A_48] : m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1(A_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_149])).

tff(c_171,plain,(
    m1_subset_1(k3_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_159])).

tff(c_82,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_29,A_1] :
      ( A_29 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_29,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_189,plain,
    ( k3_tarski('#skF_4') = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_171,c_87])).

tff(c_193,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_189])).

tff(c_196,plain,(
    ! [A_38] : k5_setfam_1(A_38,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_116])).

tff(c_215,plain,(
    ! [A_52,B_53] :
      ( k5_setfam_1(A_52,B_53) = A_52
      | ~ m1_setfam_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_223,plain,(
    ! [A_52] :
      ( k5_setfam_1(A_52,'#skF_4') = A_52
      | ~ m1_setfam_1('#skF_4',A_52) ) ),
    inference(resolution,[status(thm)],[c_47,c_215])).

tff(c_230,plain,(
    ! [A_54] :
      ( A_54 = '#skF_4'
      | ~ m1_setfam_1('#skF_4',A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_223])).

tff(c_234,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_230])).

tff(c_36,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_239,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_36])).

tff(c_243,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_239])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.22  
% 2.08/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.22  %$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.08/1.22  
% 2.08/1.22  %Foreground sorts:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Background operators:
% 2.08/1.22  
% 2.08/1.22  
% 2.08/1.22  %Foreground operators:
% 2.08/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.22  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.08/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.22  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.22  
% 2.40/1.24  tff(f_89, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 2.40/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.40/1.24  tff(f_36, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.40/1.24  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.40/1.24  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.40/1.24  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.40/1.24  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.40/1.24  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.40/1.24  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.40/1.24  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.40/1.24  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.40/1.24  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.24  tff(c_44, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.24  tff(c_38, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.40/1.24  tff(c_50, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 2.40/1.24  tff(c_40, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.40/1.24  tff(c_18, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.40/1.24  tff(c_49, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_18])).
% 2.40/1.24  tff(c_20, plain, (![A_7]: (~v1_xboole_0(k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.24  tff(c_59, plain, (~v1_xboole_0(k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_20])).
% 2.40/1.24  tff(c_22, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.24  tff(c_47, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22])).
% 2.40/1.24  tff(c_108, plain, (![A_38, B_39]: (k5_setfam_1(A_38, B_39)=k3_tarski(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.24  tff(c_116, plain, (![A_38]: (k5_setfam_1(A_38, '#skF_4')=k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_47, c_108])).
% 2.40/1.24  tff(c_136, plain, (![A_46, B_47]: (m1_subset_1(k5_setfam_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.40/1.24  tff(c_149, plain, (![A_38]: (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1(A_38)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_136])).
% 2.40/1.24  tff(c_159, plain, (![A_48]: (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1(A_48)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_149])).
% 2.40/1.24  tff(c_171, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_159])).
% 2.40/1.24  tff(c_82, plain, (![A_29, B_30]: (r2_hidden(A_29, B_30) | v1_xboole_0(B_30) | ~m1_subset_1(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.24  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.24  tff(c_87, plain, (![A_29, A_1]: (A_29=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_29, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_82, c_4])).
% 2.40/1.24  tff(c_189, plain, (k3_tarski('#skF_4')='#skF_4' | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_171, c_87])).
% 2.40/1.24  tff(c_193, plain, (k3_tarski('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_59, c_189])).
% 2.40/1.24  tff(c_196, plain, (![A_38]: (k5_setfam_1(A_38, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_116])).
% 2.40/1.24  tff(c_215, plain, (![A_52, B_53]: (k5_setfam_1(A_52, B_53)=A_52 | ~m1_setfam_1(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.40/1.24  tff(c_223, plain, (![A_52]: (k5_setfam_1(A_52, '#skF_4')=A_52 | ~m1_setfam_1('#skF_4', A_52))), inference(resolution, [status(thm)], [c_47, c_215])).
% 2.40/1.24  tff(c_230, plain, (![A_54]: (A_54='#skF_4' | ~m1_setfam_1('#skF_4', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_223])).
% 2.40/1.24  tff(c_234, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_230])).
% 2.40/1.24  tff(c_36, plain, (![A_20]: (~v1_xboole_0(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.40/1.24  tff(c_239, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_234, c_36])).
% 2.40/1.24  tff(c_243, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_239])).
% 2.40/1.24  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_243])).
% 2.40/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.24  
% 2.40/1.24  Inference rules
% 2.40/1.24  ----------------------
% 2.40/1.24  #Ref     : 0
% 2.40/1.24  #Sup     : 45
% 2.40/1.24  #Fact    : 0
% 2.40/1.24  #Define  : 0
% 2.40/1.24  #Split   : 0
% 2.40/1.24  #Chain   : 0
% 2.40/1.24  #Close   : 0
% 2.40/1.24  
% 2.40/1.24  Ordering : KBO
% 2.40/1.24  
% 2.40/1.24  Simplification rules
% 2.40/1.24  ----------------------
% 2.40/1.24  #Subsume      : 1
% 2.40/1.24  #Demod        : 20
% 2.40/1.24  #Tautology    : 21
% 2.40/1.24  #SimpNegUnit  : 3
% 2.40/1.24  #BackRed      : 4
% 2.40/1.24  
% 2.40/1.24  #Partial instantiations: 0
% 2.40/1.24  #Strategies tried      : 1
% 2.40/1.24  
% 2.40/1.24  Timing (in seconds)
% 2.40/1.24  ----------------------
% 2.40/1.24  Preprocessing        : 0.31
% 2.40/1.24  Parsing              : 0.17
% 2.40/1.24  CNF conversion       : 0.02
% 2.40/1.24  Main loop            : 0.17
% 2.40/1.24  Inferencing          : 0.06
% 2.40/1.24  Reduction            : 0.06
% 2.40/1.24  Demodulation         : 0.04
% 2.40/1.24  BG Simplification    : 0.01
% 2.40/1.24  Subsumption          : 0.03
% 2.40/1.24  Abstraction          : 0.01
% 2.40/1.24  MUC search           : 0.00
% 2.40/1.24  Cooper               : 0.00
% 2.40/1.24  Total                : 0.51
% 2.40/1.24  Index Insertion      : 0.00
% 2.40/1.24  Index Deletion       : 0.00
% 2.40/1.24  Index Matching       : 0.00
% 2.40/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
