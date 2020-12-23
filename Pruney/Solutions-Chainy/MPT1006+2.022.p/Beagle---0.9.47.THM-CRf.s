%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:05 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 181 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 320 expanded)
%              Number of equality atoms :   16 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_47,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_160,plain,(
    ! [C_47,B_48,A_49] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(B_48,A_49)))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_175,plain,(
    ! [C_47] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_160])).

tff(c_186,plain,(
    ! [C_50] :
      ( v1_xboole_0(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_207,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_186])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_94,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_47,c_94])).

tff(c_214,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_102])).

tff(c_220,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_211,c_14])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_252,plain,(
    ! [A_52,B_53,D_54,C_55] :
      ( r1_tarski(k8_relset_1(A_52,B_53,D_54,C_55),A_52)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(D_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_680,plain,(
    ! [A_100,B_101,A_102,C_103] :
      ( r1_tarski(k8_relset_1(A_100,B_101,A_102,C_103),A_100)
      | ~ v1_funct_1(A_102)
      | ~ r1_tarski(A_102,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(resolution,[status(thm)],[c_28,c_252])).

tff(c_206,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_186])).

tff(c_340,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | ~ r1_tarski(A_11,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_206])).

tff(c_688,plain,(
    ! [B_101,A_102,C_103] :
      ( v1_xboole_0(k8_relset_1('#skF_4',B_101,A_102,C_103))
      | ~ v1_funct_1(A_102)
      | ~ r1_tarski(A_102,k2_zfmisc_1('#skF_4',B_101)) ) ),
    inference(resolution,[status(thm)],[c_680,c_340])).

tff(c_712,plain,(
    ! [B_104,A_105,C_106] :
      ( v1_xboole_0(k8_relset_1('#skF_4',B_104,A_105,C_106))
      | ~ v1_funct_1(A_105)
      | ~ r1_tarski(A_105,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_688])).

tff(c_216,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_8])).

tff(c_735,plain,(
    ! [B_107,A_108,C_109] :
      ( k8_relset_1('#skF_4',B_107,A_108,C_109) = '#skF_4'
      | ~ v1_funct_1(A_108)
      | ~ r1_tarski(A_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_712,c_216])).

tff(c_745,plain,(
    ! [B_107,C_109] :
      ( k8_relset_1('#skF_4',B_107,'#skF_4',C_109) = '#skF_4'
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_214,c_735])).

tff(c_755,plain,(
    ! [B_107,C_109] : k8_relset_1('#skF_4',B_107,'#skF_4',C_109) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_745])).

tff(c_40,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_215,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_211,c_40])).

tff(c_767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.80/1.41  
% 2.80/1.41  %Foreground sorts:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Background operators:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Foreground operators:
% 2.80/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.80/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.41  
% 2.80/1.42  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.80/1.42  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.80/1.42  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.80/1.42  tff(f_74, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.80/1.42  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.80/1.42  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.42  tff(f_80, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 2.80/1.42  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.42  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.42  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.42  tff(c_47, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42])).
% 2.80/1.42  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.42  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.42  tff(c_160, plain, (![C_47, B_48, A_49]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(B_48, A_49))) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.80/1.42  tff(c_175, plain, (![C_47]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_160])).
% 2.80/1.42  tff(c_186, plain, (![C_50]: (v1_xboole_0(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_175])).
% 2.80/1.42  tff(c_207, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_47, c_186])).
% 2.80/1.42  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.80/1.42  tff(c_211, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_207, c_8])).
% 2.80/1.42  tff(c_94, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.42  tff(c_102, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_47, c_94])).
% 2.80/1.42  tff(c_214, plain, (r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_102])).
% 2.80/1.42  tff(c_220, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_211, c_14])).
% 2.80/1.42  tff(c_28, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.42  tff(c_252, plain, (![A_52, B_53, D_54, C_55]: (r1_tarski(k8_relset_1(A_52, B_53, D_54, C_55), A_52) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(D_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.42  tff(c_680, plain, (![A_100, B_101, A_102, C_103]: (r1_tarski(k8_relset_1(A_100, B_101, A_102, C_103), A_100) | ~v1_funct_1(A_102) | ~r1_tarski(A_102, k2_zfmisc_1(A_100, B_101)))), inference(resolution, [status(thm)], [c_28, c_252])).
% 2.80/1.42  tff(c_206, plain, (![A_11]: (v1_xboole_0(A_11) | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_186])).
% 2.80/1.42  tff(c_340, plain, (![A_11]: (v1_xboole_0(A_11) | ~r1_tarski(A_11, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_206])).
% 2.80/1.42  tff(c_688, plain, (![B_101, A_102, C_103]: (v1_xboole_0(k8_relset_1('#skF_4', B_101, A_102, C_103)) | ~v1_funct_1(A_102) | ~r1_tarski(A_102, k2_zfmisc_1('#skF_4', B_101)))), inference(resolution, [status(thm)], [c_680, c_340])).
% 2.80/1.42  tff(c_712, plain, (![B_104, A_105, C_106]: (v1_xboole_0(k8_relset_1('#skF_4', B_104, A_105, C_106)) | ~v1_funct_1(A_105) | ~r1_tarski(A_105, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_688])).
% 2.80/1.42  tff(c_216, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_8])).
% 2.80/1.42  tff(c_735, plain, (![B_107, A_108, C_109]: (k8_relset_1('#skF_4', B_107, A_108, C_109)='#skF_4' | ~v1_funct_1(A_108) | ~r1_tarski(A_108, '#skF_4'))), inference(resolution, [status(thm)], [c_712, c_216])).
% 2.80/1.42  tff(c_745, plain, (![B_107, C_109]: (k8_relset_1('#skF_4', B_107, '#skF_4', C_109)='#skF_4' | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_214, c_735])).
% 2.80/1.42  tff(c_755, plain, (![B_107, C_109]: (k8_relset_1('#skF_4', B_107, '#skF_4', C_109)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_745])).
% 2.80/1.42  tff(c_40, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.42  tff(c_215, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_211, c_40])).
% 2.80/1.42  tff(c_767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_755, c_215])).
% 2.80/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  Inference rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Ref     : 0
% 2.80/1.42  #Sup     : 155
% 2.80/1.42  #Fact    : 0
% 2.80/1.42  #Define  : 0
% 2.80/1.42  #Split   : 0
% 2.80/1.42  #Chain   : 0
% 2.80/1.42  #Close   : 0
% 2.80/1.42  
% 2.80/1.42  Ordering : KBO
% 2.80/1.42  
% 2.80/1.42  Simplification rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Subsume      : 26
% 2.80/1.42  #Demod        : 132
% 2.80/1.42  #Tautology    : 96
% 2.80/1.42  #SimpNegUnit  : 11
% 2.80/1.42  #BackRed      : 16
% 2.80/1.42  
% 2.80/1.42  #Partial instantiations: 0
% 2.80/1.42  #Strategies tried      : 1
% 2.80/1.42  
% 2.80/1.42  Timing (in seconds)
% 2.80/1.42  ----------------------
% 2.80/1.42  Preprocessing        : 0.31
% 2.80/1.42  Parsing              : 0.17
% 2.80/1.42  CNF conversion       : 0.02
% 2.80/1.42  Main loop            : 0.33
% 2.80/1.42  Inferencing          : 0.13
% 2.80/1.42  Reduction            : 0.10
% 2.80/1.42  Demodulation         : 0.07
% 2.80/1.42  BG Simplification    : 0.02
% 2.80/1.42  Subsumption          : 0.06
% 2.80/1.42  Abstraction          : 0.01
% 2.80/1.42  MUC search           : 0.00
% 2.80/1.42  Cooper               : 0.00
% 2.80/1.42  Total                : 0.67
% 2.80/1.42  Index Insertion      : 0.00
% 2.80/1.42  Index Deletion       : 0.00
% 2.80/1.42  Index Matching       : 0.00
% 2.80/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
