%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 157 expanded)
%              Number of leaves         :   34 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 279 expanded)
%              Number of equality atoms :   26 (  86 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_28,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_128,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_51,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_37,c_128])).

tff(c_134,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_67,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_67])).

tff(c_112,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k10_relat_1(B_46,A_47),k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    ! [A_47] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_47),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_112])).

tff(c_123,plain,(
    ! [A_48] : r1_tarski(k10_relat_1(k1_xboole_0,A_48),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_115])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_127,plain,(
    ! [A_48] : k10_relat_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_218,plain,(
    ! [A_48] : k10_relat_1('#skF_4',A_48) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_127])).

tff(c_150,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_37])).

tff(c_192,plain,(
    ! [B_57] : k2_zfmisc_1('#skF_4',B_57) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_10])).

tff(c_24,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k8_relset_1(A_11,B_12,C_13,D_14) = k10_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_286,plain,(
    ! [B_77,C_78,D_79] :
      ( k8_relset_1('#skF_4',B_77,C_78,D_79) = k10_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_24])).

tff(c_288,plain,(
    ! [B_77,D_79] : k8_relset_1('#skF_4',B_77,'#skF_4',D_79) = k10_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_150,c_286])).

tff(c_290,plain,(
    ! [B_77,D_79] : k8_relset_1('#skF_4',B_77,'#skF_4',D_79) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_288])).

tff(c_30,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_142,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_30])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.10/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.25  
% 2.17/1.26  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.17/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.26  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.26  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.17/1.26  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.17/1.26  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.17/1.26  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.17/1.26  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.17/1.26  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.17/1.26  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.17/1.26  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.17/1.26  tff(c_28, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.26  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.26  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.17/1.26  tff(c_37, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.17/1.26  tff(c_128, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.26  tff(c_130, plain, (![A_51]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_51, '#skF_4'))), inference(resolution, [status(thm)], [c_37, c_128])).
% 2.17/1.26  tff(c_134, plain, (![A_52]: (~r2_hidden(A_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_130])).
% 2.17/1.26  tff(c_139, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_134])).
% 2.17/1.26  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.26  tff(c_42, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.26  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_42])).
% 2.17/1.26  tff(c_67, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.26  tff(c_76, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_67])).
% 2.17/1.26  tff(c_112, plain, (![B_46, A_47]: (r1_tarski(k10_relat_1(B_46, A_47), k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.26  tff(c_115, plain, (![A_47]: (r1_tarski(k10_relat_1(k1_xboole_0, A_47), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_76, c_112])).
% 2.17/1.26  tff(c_123, plain, (![A_48]: (r1_tarski(k10_relat_1(k1_xboole_0, A_48), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_115])).
% 2.17/1.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.17/1.26  tff(c_127, plain, (![A_48]: (k10_relat_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_123, c_4])).
% 2.17/1.26  tff(c_218, plain, (![A_48]: (k10_relat_1('#skF_4', A_48)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_127])).
% 2.17/1.26  tff(c_150, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_37])).
% 2.17/1.26  tff(c_192, plain, (![B_57]: (k2_zfmisc_1('#skF_4', B_57)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_10])).
% 2.17/1.26  tff(c_24, plain, (![A_11, B_12, C_13, D_14]: (k8_relset_1(A_11, B_12, C_13, D_14)=k10_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.26  tff(c_286, plain, (![B_77, C_78, D_79]: (k8_relset_1('#skF_4', B_77, C_78, D_79)=k10_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_192, c_24])).
% 2.17/1.26  tff(c_288, plain, (![B_77, D_79]: (k8_relset_1('#skF_4', B_77, '#skF_4', D_79)=k10_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_150, c_286])).
% 2.17/1.26  tff(c_290, plain, (![B_77, D_79]: (k8_relset_1('#skF_4', B_77, '#skF_4', D_79)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_288])).
% 2.17/1.26  tff(c_30, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.17/1.26  tff(c_142, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_30])).
% 2.17/1.26  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_142])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 61
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 0
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 1
% 2.17/1.26  #Demod        : 49
% 2.17/1.26  #Tautology    : 47
% 2.17/1.26  #SimpNegUnit  : 0
% 2.17/1.26  #BackRed      : 15
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.26  Preprocessing        : 0.30
% 2.17/1.26  Parsing              : 0.16
% 2.17/1.26  CNF conversion       : 0.02
% 2.17/1.26  Main loop            : 0.17
% 2.17/1.27  Inferencing          : 0.06
% 2.17/1.27  Reduction            : 0.06
% 2.17/1.27  Demodulation         : 0.04
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.02
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.51
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
