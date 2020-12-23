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
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 100 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 188 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_90,plain,(
    ! [C_41,B_42,A_43] :
      ( v5_relat_1(C_41,B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_90])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_75,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(k2_relat_1(B_35),A_36)
      | ~ v5_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [B_47,A_48] :
      ( k2_xboole_0(k2_relat_1(B_47),A_48) = A_48
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [B_51,C_52,A_53] :
      ( r1_tarski(k2_relat_1(B_51),C_52)
      | ~ r1_tarski(A_53,C_52)
      | ~ v5_relat_1(B_51,A_53)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_138,plain,(
    ! [B_51] :
      ( r1_tarski(k2_relat_1(B_51),'#skF_4')
      | ~ v5_relat_1(B_51,'#skF_3')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_95,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(k1_relat_1(B_33),A_34)
      | ~ v4_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [B_49,A_50] :
      ( k2_xboole_0(k1_relat_1(B_49),A_50) = A_50
      | ~ v4_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_221,plain,(
    ! [B_62,C_63,A_64] :
      ( r1_tarski(k1_relat_1(B_62),C_63)
      | ~ r1_tarski(A_64,C_63)
      | ~ v4_relat_1(B_62,A_64)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_259,plain,(
    ! [B_67] :
      ( r1_tarski(k1_relat_1(B_67),'#skF_2')
      | ~ v4_relat_1(B_67,'#skF_1')
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_140,plain,(
    ! [C_54,A_55,B_56] :
      ( m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ r1_tarski(k2_relat_1(C_54),B_56)
      | ~ r1_tarski(k1_relat_1(C_54),A_55)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_152,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_140,c_24])).

tff(c_160,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_152])).

tff(c_161,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_264,plain,
    ( ~ v4_relat_1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_259,c_161])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_99,c_264])).

tff(c_278,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_294,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_278])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_94,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:42:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.34  
% 2.09/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.34  
% 2.36/1.34  %Foreground sorts:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Background operators:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Foreground operators:
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.36/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.36/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.34  
% 2.36/1.35  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.36/1.35  tff(f_77, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.36/1.35  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.36/1.35  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.36/1.35  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.36/1.35  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.36/1.35  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.36/1.35  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.36/1.35  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.36/1.35  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.35  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_49, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.36/1.35  tff(c_52, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.36/1.35  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 2.36/1.35  tff(c_90, plain, (![C_41, B_42, A_43]: (v5_relat_1(C_41, B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.36/1.35  tff(c_94, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_90])).
% 2.36/1.35  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_75, plain, (![B_35, A_36]: (r1_tarski(k2_relat_1(B_35), A_36) | ~v5_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.36/1.35  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.35  tff(c_100, plain, (![B_47, A_48]: (k2_xboole_0(k2_relat_1(B_47), A_48)=A_48 | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_75, c_4])).
% 2.36/1.35  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.35  tff(c_124, plain, (![B_51, C_52, A_53]: (r1_tarski(k2_relat_1(B_51), C_52) | ~r1_tarski(A_53, C_52) | ~v5_relat_1(B_51, A_53) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 2.36/1.35  tff(c_138, plain, (![B_51]: (r1_tarski(k2_relat_1(B_51), '#skF_4') | ~v5_relat_1(B_51, '#skF_3') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_26, c_124])).
% 2.36/1.35  tff(c_95, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.36/1.35  tff(c_99, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_95])).
% 2.36/1.35  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_70, plain, (![B_33, A_34]: (r1_tarski(k1_relat_1(B_33), A_34) | ~v4_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.35  tff(c_112, plain, (![B_49, A_50]: (k2_xboole_0(k1_relat_1(B_49), A_50)=A_50 | ~v4_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_70, c_4])).
% 2.36/1.35  tff(c_221, plain, (![B_62, C_63, A_64]: (r1_tarski(k1_relat_1(B_62), C_63) | ~r1_tarski(A_64, C_63) | ~v4_relat_1(B_62, A_64) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2])).
% 2.36/1.35  tff(c_259, plain, (![B_67]: (r1_tarski(k1_relat_1(B_67), '#skF_2') | ~v4_relat_1(B_67, '#skF_1') | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_28, c_221])).
% 2.36/1.35  tff(c_140, plain, (![C_54, A_55, B_56]: (m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~r1_tarski(k2_relat_1(C_54), B_56) | ~r1_tarski(k1_relat_1(C_54), A_55) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.35  tff(c_24, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_152, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_140, c_24])).
% 2.36/1.35  tff(c_160, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_152])).
% 2.36/1.35  tff(c_161, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_160])).
% 2.36/1.35  tff(c_264, plain, (~v4_relat_1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_259, c_161])).
% 2.36/1.35  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_99, c_264])).
% 2.36/1.35  tff(c_278, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_160])).
% 2.36/1.35  tff(c_294, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_138, c_278])).
% 2.36/1.35  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_94, c_294])).
% 2.36/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  Inference rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Ref     : 0
% 2.36/1.35  #Sup     : 65
% 2.36/1.35  #Fact    : 0
% 2.36/1.35  #Define  : 0
% 2.36/1.35  #Split   : 1
% 2.36/1.35  #Chain   : 0
% 2.36/1.35  #Close   : 0
% 2.36/1.35  
% 2.36/1.35  Ordering : KBO
% 2.36/1.35  
% 2.36/1.35  Simplification rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Subsume      : 2
% 2.36/1.35  #Demod        : 9
% 2.36/1.35  #Tautology    : 15
% 2.36/1.35  #SimpNegUnit  : 0
% 2.36/1.35  #BackRed      : 0
% 2.36/1.35  
% 2.36/1.35  #Partial instantiations: 0
% 2.36/1.35  #Strategies tried      : 1
% 2.36/1.35  
% 2.36/1.35  Timing (in seconds)
% 2.36/1.35  ----------------------
% 2.36/1.36  Preprocessing        : 0.30
% 2.36/1.36  Parsing              : 0.17
% 2.36/1.36  CNF conversion       : 0.02
% 2.36/1.36  Main loop            : 0.23
% 2.36/1.36  Inferencing          : 0.09
% 2.36/1.36  Reduction            : 0.06
% 2.36/1.36  Demodulation         : 0.04
% 2.36/1.36  BG Simplification    : 0.01
% 2.36/1.36  Subsumption          : 0.04
% 2.36/1.36  Abstraction          : 0.01
% 2.36/1.36  MUC search           : 0.00
% 2.36/1.36  Cooper               : 0.00
% 2.36/1.36  Total                : 0.56
% 2.36/1.36  Index Insertion      : 0.00
% 2.36/1.36  Index Deletion       : 0.00
% 2.36/1.36  Index Matching       : 0.00
% 2.36/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
