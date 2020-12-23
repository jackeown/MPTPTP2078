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
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 117 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_43])).

tff(c_53,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_16])).

tff(c_63,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_72,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_68])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    k2_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [A_49] :
      ( r1_xboole_0(A_49,k1_relat_1('#skF_4'))
      | ~ r1_xboole_0(A_49,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k7_relat_1(A_11,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_91,plain,(
    ! [A_49] :
      ( k7_relat_1('#skF_4',A_49) = k1_xboole_0
      | ~ v1_relat_1('#skF_4')
      | ~ r1_xboole_0(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_88,c_14])).

tff(c_95,plain,(
    ! [A_50] :
      ( k7_relat_1('#skF_4',A_50) = k1_xboole_0
      | ~ r1_xboole_0(A_50,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_99,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_172,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k5_relset_1(A_57,B_58,C_59,D_60) = k7_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_175,plain,(
    ! [D_60] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_60) = k7_relat_1('#skF_4',D_60) ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_26,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_176,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_26])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.25  
% 2.03/1.25  %Foreground sorts:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Background operators:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Foreground operators:
% 2.03/1.25  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.03/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.03/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.25  
% 2.08/1.26  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.08/1.26  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.08/1.26  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.08/1.26  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.08/1.26  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.08/1.26  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.08/1.26  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.26  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.08/1.26  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.08/1.26  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.08/1.26  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.26  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.26  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.26  tff(c_40, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.26  tff(c_43, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.08/1.26  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_43])).
% 2.08/1.26  tff(c_53, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.26  tff(c_57, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_53])).
% 2.08/1.26  tff(c_16, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.08/1.26  tff(c_60, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_57, c_16])).
% 2.08/1.26  tff(c_63, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 2.08/1.26  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.08/1.26  tff(c_68, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_18])).
% 2.08/1.26  tff(c_72, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_68])).
% 2.08/1.26  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.26  tff(c_77, plain, (k2_xboole_0(k1_relat_1('#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_72, c_2])).
% 2.08/1.26  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.26  tff(c_88, plain, (![A_49]: (r1_xboole_0(A_49, k1_relat_1('#skF_4')) | ~r1_xboole_0(A_49, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_8])).
% 2.08/1.26  tff(c_14, plain, (![A_11, B_13]: (k7_relat_1(A_11, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.26  tff(c_91, plain, (![A_49]: (k7_relat_1('#skF_4', A_49)=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_xboole_0(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_14])).
% 2.08/1.26  tff(c_95, plain, (![A_50]: (k7_relat_1('#skF_4', A_50)=k1_xboole_0 | ~r1_xboole_0(A_50, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_91])).
% 2.08/1.26  tff(c_99, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_95])).
% 2.08/1.26  tff(c_172, plain, (![A_57, B_58, C_59, D_60]: (k5_relset_1(A_57, B_58, C_59, D_60)=k7_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.08/1.26  tff(c_175, plain, (![D_60]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_60)=k7_relat_1('#skF_4', D_60))), inference(resolution, [status(thm)], [c_30, c_172])).
% 2.08/1.26  tff(c_26, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.08/1.26  tff(c_176, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_26])).
% 2.08/1.26  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_176])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 36
% 2.08/1.27  #Fact    : 0
% 2.08/1.27  #Define  : 0
% 2.08/1.27  #Split   : 1
% 2.08/1.27  #Chain   : 0
% 2.08/1.27  #Close   : 0
% 2.08/1.27  
% 2.08/1.27  Ordering : KBO
% 2.08/1.27  
% 2.08/1.27  Simplification rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Subsume      : 0
% 2.08/1.27  #Demod        : 11
% 2.08/1.27  #Tautology    : 20
% 2.08/1.27  #SimpNegUnit  : 0
% 2.08/1.27  #BackRed      : 1
% 2.08/1.27  
% 2.08/1.27  #Partial instantiations: 0
% 2.08/1.27  #Strategies tried      : 1
% 2.08/1.27  
% 2.08/1.27  Timing (in seconds)
% 2.08/1.27  ----------------------
% 2.08/1.27  Preprocessing        : 0.30
% 2.08/1.27  Parsing              : 0.16
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.15
% 2.08/1.27  Inferencing          : 0.06
% 2.08/1.27  Reduction            : 0.05
% 2.08/1.27  Demodulation         : 0.03
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.02
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.48
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
