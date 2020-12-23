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
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 163 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 249 expanded)
%              Number of equality atoms :   21 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_8])).

tff(c_24,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_43,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38])).

tff(c_134,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_136,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_134])).

tff(c_143,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_136])).

tff(c_149,plain,(
    ! [B_44] : r1_tarski('#skF_4',B_44) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_18,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_92])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_101])).

tff(c_32,plain,(
    ! [A_19] : k10_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_167,plain,(
    ! [A_19] : k10_relat_1('#skF_4',A_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_32])).

tff(c_26,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_168,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_26])).

tff(c_253,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k8_relset_1(A_59,B_60,C_61,D_62) = k10_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_260,plain,(
    ! [A_59,B_60,D_62] : k8_relset_1(A_59,B_60,'#skF_4',D_62) = k10_relat_1('#skF_4',D_62) ),
    inference(resolution,[status(thm)],[c_168,c_253])).

tff(c_262,plain,(
    ! [A_59,B_60,D_62] : k8_relset_1(A_59,B_60,'#skF_4',D_62) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_260])).

tff(c_36,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_164,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_36])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:08:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.61  
% 2.53/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.62  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.53/1.62  
% 2.53/1.62  %Foreground sorts:
% 2.53/1.62  
% 2.53/1.62  
% 2.53/1.62  %Background operators:
% 2.53/1.62  
% 2.53/1.62  
% 2.53/1.62  %Foreground operators:
% 2.53/1.62  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.53/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.53/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.53/1.62  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.62  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.53/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.62  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.62  
% 2.53/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.53/1.64  tff(f_33, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.53/1.64  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.64  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.53/1.64  tff(f_81, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.53/1.64  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.53/1.64  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.64  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.64  tff(f_68, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.53/1.64  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.53/1.64  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.53/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.64  tff(c_8, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.64  tff(c_77, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.64  tff(c_81, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_77])).
% 2.53/1.64  tff(c_82, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_8])).
% 2.53/1.64  tff(c_24, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.64  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.64  tff(c_43, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38])).
% 2.53/1.64  tff(c_134, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.53/1.64  tff(c_136, plain, (![A_42]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_134])).
% 2.53/1.64  tff(c_143, plain, (![A_43]: (~r2_hidden(A_43, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_136])).
% 2.53/1.64  tff(c_149, plain, (![B_44]: (r1_tarski('#skF_4', B_44))), inference(resolution, [status(thm)], [c_6, c_143])).
% 2.53/1.64  tff(c_18, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.64  tff(c_92, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.64  tff(c_101, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_92])).
% 2.53/1.64  tff(c_156, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_149, c_101])).
% 2.53/1.64  tff(c_32, plain, (![A_19]: (k10_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.64  tff(c_167, plain, (![A_19]: (k10_relat_1('#skF_4', A_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_32])).
% 2.53/1.64  tff(c_26, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.64  tff(c_168, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_26])).
% 2.53/1.64  tff(c_253, plain, (![A_59, B_60, C_61, D_62]: (k8_relset_1(A_59, B_60, C_61, D_62)=k10_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.64  tff(c_260, plain, (![A_59, B_60, D_62]: (k8_relset_1(A_59, B_60, '#skF_4', D_62)=k10_relat_1('#skF_4', D_62))), inference(resolution, [status(thm)], [c_168, c_253])).
% 2.53/1.64  tff(c_262, plain, (![A_59, B_60, D_62]: (k8_relset_1(A_59, B_60, '#skF_4', D_62)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_260])).
% 2.53/1.64  tff(c_36, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.64  tff(c_164, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_36])).
% 2.53/1.64  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_164])).
% 2.53/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.64  
% 2.53/1.64  Inference rules
% 2.53/1.64  ----------------------
% 2.53/1.64  #Ref     : 0
% 2.53/1.64  #Sup     : 47
% 2.53/1.64  #Fact    : 0
% 2.53/1.64  #Define  : 0
% 2.53/1.64  #Split   : 0
% 2.53/1.64  #Chain   : 0
% 2.53/1.64  #Close   : 0
% 2.53/1.64  
% 2.53/1.64  Ordering : KBO
% 2.53/1.64  
% 2.53/1.64  Simplification rules
% 2.53/1.64  ----------------------
% 2.53/1.64  #Subsume      : 4
% 2.53/1.64  #Demod        : 31
% 2.53/1.64  #Tautology    : 37
% 2.53/1.64  #SimpNegUnit  : 0
% 2.53/1.64  #BackRed      : 15
% 2.53/1.64  
% 2.53/1.64  #Partial instantiations: 0
% 2.53/1.64  #Strategies tried      : 1
% 2.53/1.64  
% 2.53/1.64  Timing (in seconds)
% 2.53/1.64  ----------------------
% 2.53/1.64  Preprocessing        : 0.49
% 2.53/1.64  Parsing              : 0.26
% 2.53/1.64  CNF conversion       : 0.03
% 2.53/1.64  Main loop            : 0.27
% 2.53/1.64  Inferencing          : 0.10
% 2.53/1.64  Reduction            : 0.09
% 2.53/1.64  Demodulation         : 0.07
% 2.53/1.64  BG Simplification    : 0.02
% 2.53/1.64  Subsumption          : 0.04
% 2.53/1.64  Abstraction          : 0.02
% 2.53/1.64  MUC search           : 0.00
% 2.53/1.64  Cooper               : 0.00
% 2.53/1.64  Total                : 0.81
% 2.53/1.65  Index Insertion      : 0.00
% 2.53/1.65  Index Deletion       : 0.00
% 2.53/1.65  Index Matching       : 0.00
% 2.53/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
