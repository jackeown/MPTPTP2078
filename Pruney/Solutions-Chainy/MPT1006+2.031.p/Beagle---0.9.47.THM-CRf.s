%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 361 expanded)
%              Number of leaves         :   27 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 628 expanded)
%              Number of equality atoms :   38 ( 282 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_69,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41,c_69])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_81,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_41])).

tff(c_82,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_8])).

tff(c_139,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1('#skF_3',B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_139])).

tff(c_181,plain,(
    ! [B_40] : k1_relset_1('#skF_3',B_40,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_174])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_38])).

tff(c_30,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_277,plain,(
    ! [B_67,C_68] :
      ( k1_relset_1('#skF_3',B_67,C_68) = '#skF_3'
      | ~ v1_funct_2(C_68,'#skF_3',B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_77,c_42])).

tff(c_282,plain,
    ( k1_relset_1('#skF_3','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_277])).

tff(c_289,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_181,c_282])).

tff(c_290,plain,(
    ! [B_40] : k1_relset_1('#skF_3',B_40,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_181])).

tff(c_217,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k8_relset_1(A_50,B_51,C_52,D_53) = k10_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_248,plain,(
    ! [B_62,C_63,D_64] :
      ( k8_relset_1('#skF_3',B_62,C_63,D_64) = k10_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_217])).

tff(c_255,plain,(
    ! [B_62,D_64] : k8_relset_1('#skF_3',B_62,'#skF_3',D_64) = k10_relat_1('#skF_3',D_64) ),
    inference(resolution,[status(thm)],[c_81,c_248])).

tff(c_361,plain,(
    ! [A_83,B_84,C_85] :
      ( k8_relset_1(A_83,B_84,C_85,B_84) = k1_relset_1(A_83,B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_397,plain,(
    ! [B_93,C_94] :
      ( k8_relset_1('#skF_3',B_93,C_94,B_93) = k1_relset_1('#skF_3',B_93,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_361])).

tff(c_402,plain,(
    ! [B_93] : k8_relset_1('#skF_3',B_93,'#skF_3',B_93) = k1_relset_1('#skF_3',B_93,'#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_397])).

tff(c_405,plain,(
    ! [B_93] : k10_relat_1('#skF_3',B_93) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_255,c_402])).

tff(c_34,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_79,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_34])).

tff(c_256,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_79])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.40  
% 2.35/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.41  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.41  
% 2.35/1.41  %Foreground sorts:
% 2.35/1.41  
% 2.35/1.41  
% 2.35/1.41  %Background operators:
% 2.35/1.41  
% 2.35/1.41  
% 2.35/1.41  %Foreground operators:
% 2.35/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.35/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.35/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.41  
% 2.35/1.42  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.35/1.42  tff(f_80, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.35/1.42  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.35/1.42  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.35/1.42  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.42  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.35/1.42  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.35/1.42  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.35/1.42  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.42  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.35/1.42  tff(c_41, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 2.35/1.42  tff(c_69, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.42  tff(c_73, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_41, c_69])).
% 2.35/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.42  tff(c_77, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.35/1.42  tff(c_81, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_41])).
% 2.35/1.42  tff(c_82, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_8])).
% 2.35/1.42  tff(c_139, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.42  tff(c_174, plain, (![B_40, C_41]: (k1_relset_1('#skF_3', B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_139])).
% 2.35/1.42  tff(c_181, plain, (![B_40]: (k1_relset_1('#skF_3', B_40, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_174])).
% 2.35/1.42  tff(c_38, plain, (v1_funct_2('#skF_3', k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.35/1.42  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_38])).
% 2.35/1.42  tff(c_30, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.35/1.42  tff(c_42, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_30])).
% 2.35/1.42  tff(c_277, plain, (![B_67, C_68]: (k1_relset_1('#skF_3', B_67, C_68)='#skF_3' | ~v1_funct_2(C_68, '#skF_3', B_67) | ~m1_subset_1(C_68, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_77, c_42])).
% 2.35/1.42  tff(c_282, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_277])).
% 2.35/1.42  tff(c_289, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_181, c_282])).
% 2.35/1.42  tff(c_290, plain, (![B_40]: (k1_relset_1('#skF_3', B_40, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_181])).
% 2.35/1.42  tff(c_217, plain, (![A_50, B_51, C_52, D_53]: (k8_relset_1(A_50, B_51, C_52, D_53)=k10_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.42  tff(c_248, plain, (![B_62, C_63, D_64]: (k8_relset_1('#skF_3', B_62, C_63, D_64)=k10_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_217])).
% 2.35/1.42  tff(c_255, plain, (![B_62, D_64]: (k8_relset_1('#skF_3', B_62, '#skF_3', D_64)=k10_relat_1('#skF_3', D_64))), inference(resolution, [status(thm)], [c_81, c_248])).
% 2.35/1.42  tff(c_361, plain, (![A_83, B_84, C_85]: (k8_relset_1(A_83, B_84, C_85, B_84)=k1_relset_1(A_83, B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.42  tff(c_397, plain, (![B_93, C_94]: (k8_relset_1('#skF_3', B_93, C_94, B_93)=k1_relset_1('#skF_3', B_93, C_94) | ~m1_subset_1(C_94, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_361])).
% 2.35/1.42  tff(c_402, plain, (![B_93]: (k8_relset_1('#skF_3', B_93, '#skF_3', B_93)=k1_relset_1('#skF_3', B_93, '#skF_3'))), inference(resolution, [status(thm)], [c_81, c_397])).
% 2.35/1.42  tff(c_405, plain, (![B_93]: (k10_relat_1('#skF_3', B_93)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_255, c_402])).
% 2.35/1.42  tff(c_34, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.35/1.42  tff(c_79, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_34])).
% 2.35/1.42  tff(c_256, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_255, c_79])).
% 2.35/1.42  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_256])).
% 2.35/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.42  
% 2.35/1.42  Inference rules
% 2.35/1.42  ----------------------
% 2.35/1.42  #Ref     : 0
% 2.35/1.42  #Sup     : 85
% 2.35/1.42  #Fact    : 0
% 2.35/1.42  #Define  : 0
% 2.35/1.42  #Split   : 0
% 2.35/1.42  #Chain   : 0
% 2.35/1.42  #Close   : 0
% 2.35/1.42  
% 2.35/1.42  Ordering : KBO
% 2.35/1.42  
% 2.35/1.42  Simplification rules
% 2.35/1.42  ----------------------
% 2.35/1.42  #Subsume      : 5
% 2.35/1.42  #Demod        : 66
% 2.35/1.42  #Tautology    : 53
% 2.35/1.42  #SimpNegUnit  : 0
% 2.35/1.42  #BackRed      : 13
% 2.35/1.42  
% 2.35/1.42  #Partial instantiations: 0
% 2.35/1.42  #Strategies tried      : 1
% 2.35/1.42  
% 2.35/1.42  Timing (in seconds)
% 2.35/1.42  ----------------------
% 2.35/1.43  Preprocessing        : 0.32
% 2.35/1.43  Parsing              : 0.17
% 2.35/1.43  CNF conversion       : 0.02
% 2.35/1.43  Main loop            : 0.31
% 2.35/1.43  Inferencing          : 0.10
% 2.35/1.43  Reduction            : 0.11
% 2.35/1.43  Demodulation         : 0.08
% 2.35/1.43  BG Simplification    : 0.02
% 2.35/1.43  Subsumption          : 0.06
% 2.35/1.43  Abstraction          : 0.02
% 2.35/1.43  MUC search           : 0.00
% 2.35/1.43  Cooper               : 0.00
% 2.35/1.43  Total                : 0.67
% 2.35/1.43  Index Insertion      : 0.00
% 2.35/1.43  Index Deletion       : 0.00
% 2.35/1.43  Index Matching       : 0.00
% 2.35/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
