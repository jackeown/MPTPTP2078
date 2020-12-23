%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:15 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 127 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 214 expanded)
%              Number of equality atoms :   42 ( 119 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_43,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    ! [A_31] :
      ( k6_domain_1(A_31,'#skF_4'(A_31)) = A_31
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_4'(A_31),A_31)
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_504,plain,(
    ! [A_86,B_87] :
      ( k6_domain_1(A_86,B_87) = k1_tarski(B_87)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_885,plain,(
    ! [A_122] :
      ( k6_domain_1(A_122,'#skF_4'(A_122)) = k1_tarski('#skF_4'(A_122))
      | ~ v1_zfmisc_1(A_122)
      | v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_54,c_504])).

tff(c_9234,plain,(
    ! [A_439] :
      ( k1_tarski('#skF_4'(A_439)) = A_439
      | ~ v1_zfmisc_1(A_439)
      | v1_xboole_0(A_439)
      | ~ v1_zfmisc_1(A_439)
      | v1_xboole_0(A_439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_885])).

tff(c_56,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_336,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_348,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k2_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_336])).

tff(c_351,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_348])).

tff(c_58,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_240,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_244,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_240])).

tff(c_345,plain,(
    k5_xboole_0('#skF_6',k1_xboole_0) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_336])).

tff(c_361,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_345])).

tff(c_529,plain,(
    ! [C_91,B_92,A_93] :
      ( k1_xboole_0 = C_91
      | k1_xboole_0 = B_92
      | C_91 = B_92
      | k2_xboole_0(B_92,C_91) != k1_tarski(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_532,plain,(
    ! [A_93] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_6'
      | '#skF_5' = '#skF_6'
      | k1_tarski(A_93) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_529])).

tff(c_545,plain,(
    ! [A_93] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_6'
      | k1_tarski(A_93) != '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_532])).

tff(c_548,plain,(
    ! [A_93] : k1_tarski(A_93) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_9253,plain,(
    ! [A_440] :
      ( A_440 != '#skF_6'
      | ~ v1_zfmisc_1(A_440)
      | v1_xboole_0(A_440)
      | ~ v1_zfmisc_1(A_440)
      | v1_xboole_0(A_440) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9234,c_548])).

tff(c_9255,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_9253])).

tff(c_9258,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9255])).

tff(c_9260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_9258])).

tff(c_9261,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_9262,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9261])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9303,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9262,c_26])).

tff(c_9305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_9303])).

tff(c_9306,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9261])).

tff(c_9319,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9306,c_26])).

tff(c_9321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_9319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:05:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.53/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.74  
% 7.53/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.74  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 7.53/2.74  
% 7.53/2.74  %Foreground sorts:
% 7.53/2.74  
% 7.53/2.74  
% 7.53/2.74  %Background operators:
% 7.53/2.74  
% 7.53/2.74  
% 7.53/2.74  %Foreground operators:
% 7.53/2.74  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.53/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.53/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.53/2.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.53/2.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.53/2.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.53/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.53/2.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.53/2.74  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.53/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.53/2.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.53/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.53/2.74  tff('#skF_6', type, '#skF_6': $i).
% 7.53/2.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.53/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.53/2.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.53/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.53/2.74  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.53/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.53/2.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.53/2.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.53/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.53/2.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.53/2.74  
% 7.53/2.75  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 7.53/2.75  tff(f_92, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 7.53/2.75  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.53/2.75  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.53/2.75  tff(f_57, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 7.53/2.75  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.53/2.75  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.53/2.75  tff(f_73, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 7.53/2.75  tff(f_43, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.53/2.75  tff(c_62, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.75  tff(c_64, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.75  tff(c_60, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.75  tff(c_52, plain, (![A_31]: (k6_domain_1(A_31, '#skF_4'(A_31))=A_31 | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.53/2.75  tff(c_54, plain, (![A_31]: (m1_subset_1('#skF_4'(A_31), A_31) | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.53/2.75  tff(c_504, plain, (![A_86, B_87]: (k6_domain_1(A_86, B_87)=k1_tarski(B_87) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.53/2.75  tff(c_885, plain, (![A_122]: (k6_domain_1(A_122, '#skF_4'(A_122))=k1_tarski('#skF_4'(A_122)) | ~v1_zfmisc_1(A_122) | v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_54, c_504])).
% 7.53/2.75  tff(c_9234, plain, (![A_439]: (k1_tarski('#skF_4'(A_439))=A_439 | ~v1_zfmisc_1(A_439) | v1_xboole_0(A_439) | ~v1_zfmisc_1(A_439) | v1_xboole_0(A_439))), inference(superposition, [status(thm), theory('equality')], [c_52, c_885])).
% 7.53/2.75  tff(c_56, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.75  tff(c_32, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.53/2.75  tff(c_38, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.53/2.75  tff(c_336, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k4_xboole_0(B_62, A_61))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.53/2.75  tff(c_348, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k2_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_336])).
% 7.53/2.75  tff(c_351, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_348])).
% 7.53/2.75  tff(c_58, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.75  tff(c_240, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.53/2.75  tff(c_244, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_240])).
% 7.53/2.75  tff(c_345, plain, (k5_xboole_0('#skF_6', k1_xboole_0)=k2_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_244, c_336])).
% 7.53/2.75  tff(c_361, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_345])).
% 7.53/2.75  tff(c_529, plain, (![C_91, B_92, A_93]: (k1_xboole_0=C_91 | k1_xboole_0=B_92 | C_91=B_92 | k2_xboole_0(B_92, C_91)!=k1_tarski(A_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.53/2.75  tff(c_532, plain, (![A_93]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | '#skF_5'='#skF_6' | k1_tarski(A_93)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_361, c_529])).
% 7.53/2.75  tff(c_545, plain, (![A_93]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k1_tarski(A_93)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_532])).
% 7.53/2.75  tff(c_548, plain, (![A_93]: (k1_tarski(A_93)!='#skF_6')), inference(splitLeft, [status(thm)], [c_545])).
% 7.53/2.75  tff(c_9253, plain, (![A_440]: (A_440!='#skF_6' | ~v1_zfmisc_1(A_440) | v1_xboole_0(A_440) | ~v1_zfmisc_1(A_440) | v1_xboole_0(A_440))), inference(superposition, [status(thm), theory('equality')], [c_9234, c_548])).
% 7.53/2.75  tff(c_9255, plain, (~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_9253])).
% 7.53/2.75  tff(c_9258, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9255])).
% 7.53/2.75  tff(c_9260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_9258])).
% 7.53/2.75  tff(c_9261, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_545])).
% 7.53/2.75  tff(c_9262, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_9261])).
% 7.53/2.75  tff(c_26, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.53/2.75  tff(c_9303, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9262, c_26])).
% 7.53/2.75  tff(c_9305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_9303])).
% 7.53/2.75  tff(c_9306, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_9261])).
% 7.53/2.75  tff(c_9319, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9306, c_26])).
% 7.53/2.75  tff(c_9321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_9319])).
% 7.53/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.75  
% 7.53/2.75  Inference rules
% 7.53/2.75  ----------------------
% 7.53/2.75  #Ref     : 0
% 7.53/2.75  #Sup     : 2471
% 7.53/2.75  #Fact    : 0
% 7.53/2.75  #Define  : 0
% 7.53/2.75  #Split   : 9
% 7.53/2.75  #Chain   : 0
% 7.53/2.75  #Close   : 0
% 7.53/2.75  
% 7.53/2.75  Ordering : KBO
% 7.53/2.75  
% 7.53/2.75  Simplification rules
% 7.53/2.75  ----------------------
% 7.53/2.75  #Subsume      : 1121
% 7.53/2.75  #Demod        : 1018
% 7.53/2.75  #Tautology    : 832
% 7.53/2.75  #SimpNegUnit  : 103
% 7.53/2.75  #BackRed      : 67
% 7.53/2.75  
% 7.53/2.75  #Partial instantiations: 0
% 7.53/2.75  #Strategies tried      : 1
% 7.53/2.75  
% 7.53/2.75  Timing (in seconds)
% 7.53/2.75  ----------------------
% 7.53/2.76  Preprocessing        : 0.38
% 7.53/2.76  Parsing              : 0.20
% 7.53/2.76  CNF conversion       : 0.03
% 7.53/2.76  Main loop            : 1.59
% 7.53/2.76  Inferencing          : 0.47
% 7.53/2.76  Reduction            : 0.46
% 7.53/2.76  Demodulation         : 0.34
% 7.53/2.76  BG Simplification    : 0.05
% 7.53/2.76  Subsumption          : 0.49
% 7.53/2.76  Abstraction          : 0.06
% 7.53/2.76  MUC search           : 0.00
% 7.53/2.76  Cooper               : 0.00
% 7.53/2.76  Total                : 2.00
% 7.53/2.76  Index Insertion      : 0.00
% 7.53/2.76  Index Deletion       : 0.00
% 7.53/2.76  Index Matching       : 0.00
% 7.53/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
