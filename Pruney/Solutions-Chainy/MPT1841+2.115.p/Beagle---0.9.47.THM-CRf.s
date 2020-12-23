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
% DateTime   : Thu Dec  3 10:28:43 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 141 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_86,plain,(
    ! [A_38,B_39] :
      ( k6_domain_1(A_38,B_39) = k1_tarski(B_39)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_89,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_92,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_89])).

tff(c_28,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_93,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_28])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_162,plain,(
    ! [B_43,A_44] :
      ( ~ v1_subset_1(B_43,A_44)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_zfmisc_1(A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_173,plain,(
    ! [A_45,B_46] :
      ( ~ v1_subset_1(k6_domain_1(A_45,B_46),A_45)
      | v1_xboole_0(k6_domain_1(A_45,B_46))
      | ~ v1_zfmisc_1(A_45)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_176,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_173])).

tff(c_178,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_92,c_93,c_176])).

tff(c_179,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_178])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_183,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ r2_hidden(B_9,A_8)
      | k4_xboole_0(A_8,k1_tarski(B_9)) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_195,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2',A_8)
      | k4_xboole_0(A_8,k1_xboole_0) != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_12])).

tff(c_208,plain,(
    ! [A_48] : ~ r2_hidden('#skF_2',A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_195])).

tff(c_240,plain,(
    ! [B_49] :
      ( v1_xboole_0(B_49)
      | ~ m1_subset_1('#skF_2',B_49) ) ),
    inference(resolution,[status(thm)],[c_18,c_208])).

tff(c_243,plain,(
    v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_240])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_243])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.24  
% 2.27/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.24  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.27/1.24  
% 2.27/1.24  %Foreground sorts:
% 2.27/1.24  
% 2.27/1.24  
% 2.27/1.24  %Background operators:
% 2.27/1.24  
% 2.27/1.24  
% 2.27/1.24  %Foreground operators:
% 2.27/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.24  
% 2.27/1.25  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.27/1.25  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.27/1.25  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.27/1.25  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.27/1.25  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.27/1.25  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.27/1.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.25  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.27/1.25  tff(c_32, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.25  tff(c_30, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.25  tff(c_18, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.25  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.25  tff(c_26, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.25  tff(c_86, plain, (![A_38, B_39]: (k6_domain_1(A_38, B_39)=k1_tarski(B_39) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.25  tff(c_89, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_86])).
% 2.27/1.25  tff(c_92, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_89])).
% 2.27/1.25  tff(c_28, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.27/1.25  tff(c_93, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_28])).
% 2.27/1.25  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k6_domain_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.25  tff(c_162, plain, (![B_43, A_44]: (~v1_subset_1(B_43, A_44) | v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_zfmisc_1(A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.27/1.25  tff(c_173, plain, (![A_45, B_46]: (~v1_subset_1(k6_domain_1(A_45, B_46), A_45) | v1_xboole_0(k6_domain_1(A_45, B_46)) | ~v1_zfmisc_1(A_45) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_20, c_162])).
% 2.27/1.25  tff(c_176, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_92, c_173])).
% 2.27/1.25  tff(c_178, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_92, c_93, c_176])).
% 2.27/1.25  tff(c_179, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_178])).
% 2.27/1.25  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.25  tff(c_183, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_179, c_2])).
% 2.27/1.25  tff(c_12, plain, (![B_9, A_8]: (~r2_hidden(B_9, A_8) | k4_xboole_0(A_8, k1_tarski(B_9))!=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.25  tff(c_195, plain, (![A_8]: (~r2_hidden('#skF_2', A_8) | k4_xboole_0(A_8, k1_xboole_0)!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_183, c_12])).
% 2.27/1.25  tff(c_208, plain, (![A_48]: (~r2_hidden('#skF_2', A_48))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_195])).
% 2.27/1.25  tff(c_240, plain, (![B_49]: (v1_xboole_0(B_49) | ~m1_subset_1('#skF_2', B_49))), inference(resolution, [status(thm)], [c_18, c_208])).
% 2.27/1.25  tff(c_243, plain, (v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_240])).
% 2.27/1.25  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_243])).
% 2.27/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.25  
% 2.27/1.25  Inference rules
% 2.27/1.25  ----------------------
% 2.27/1.25  #Ref     : 0
% 2.27/1.25  #Sup     : 45
% 2.27/1.25  #Fact    : 0
% 2.27/1.25  #Define  : 0
% 2.27/1.25  #Split   : 1
% 2.27/1.25  #Chain   : 0
% 2.27/1.25  #Close   : 0
% 2.27/1.25  
% 2.27/1.25  Ordering : KBO
% 2.27/1.25  
% 2.27/1.25  Simplification rules
% 2.27/1.25  ----------------------
% 2.27/1.25  #Subsume      : 2
% 2.27/1.25  #Demod        : 33
% 2.27/1.25  #Tautology    : 31
% 2.27/1.25  #SimpNegUnit  : 8
% 2.27/1.25  #BackRed      : 7
% 2.27/1.25  
% 2.27/1.25  #Partial instantiations: 0
% 2.27/1.25  #Strategies tried      : 1
% 2.27/1.25  
% 2.27/1.25  Timing (in seconds)
% 2.27/1.25  ----------------------
% 2.27/1.25  Preprocessing        : 0.31
% 2.27/1.25  Parsing              : 0.17
% 2.27/1.25  CNF conversion       : 0.02
% 2.27/1.25  Main loop            : 0.18
% 2.27/1.25  Inferencing          : 0.07
% 2.27/1.25  Reduction            : 0.05
% 2.27/1.25  Demodulation         : 0.04
% 2.27/1.25  BG Simplification    : 0.01
% 2.27/1.25  Subsumption          : 0.03
% 2.27/1.25  Abstraction          : 0.01
% 2.27/1.25  MUC search           : 0.00
% 2.27/1.25  Cooper               : 0.00
% 2.27/1.26  Total                : 0.51
% 2.27/1.26  Index Insertion      : 0.00
% 2.27/1.26  Index Deletion       : 0.00
% 2.27/1.26  Index Matching       : 0.00
% 2.27/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
