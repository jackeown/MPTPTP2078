%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:51 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 124 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 201 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_77,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_87,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_83])).

tff(c_45,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_50,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    k2_xboole_0('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_50])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k7_relat_1(B_20,A_19),B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_214,plain,(
    ! [B_59,A_60] :
      ( k2_xboole_0(k7_relat_1(B_59,A_60),B_59) = B_59
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(k2_xboole_0(A_44,B_46),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_47,B_48] : r1_tarski(A_47,k2_xboole_0(A_47,B_48)) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [A_3,B_4,B_48] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_48)) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_641,plain,(
    ! [B_112,A_113,B_114] :
      ( r1_tarski(k7_relat_1(B_112,A_113),k2_xboole_0(B_112,B_114))
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_126])).

tff(c_661,plain,(
    ! [A_113] :
      ( r1_tarski(k7_relat_1('#skF_4',A_113),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_641])).

tff(c_672,plain,(
    ! [A_115] : r1_tarski(k7_relat_1('#skF_4',A_115),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_661])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(A_8)
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_683,plain,(
    ! [A_115] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_115))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_672,c_84])).

tff(c_692,plain,(
    ! [A_115] : v1_relat_1(k7_relat_1('#skF_4',A_115)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_683])).

tff(c_392,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_400,plain,(
    ! [A_8,B_77,A_78] :
      ( v5_relat_1(A_8,B_77)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_78,B_77)) ) ),
    inference(resolution,[status(thm)],[c_14,c_392])).

tff(c_688,plain,(
    ! [A_115] : v5_relat_1(k7_relat_1('#skF_4',A_115),'#skF_2') ),
    inference(resolution,[status(thm)],[c_672,c_400])).

tff(c_340,plain,(
    ! [B_69,A_70] :
      ( k2_relat_1(k7_relat_1(B_69,A_70)) = k9_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2159,plain,(
    ! [B_229,A_230,A_231] :
      ( r1_tarski(k9_relat_1(B_229,A_230),A_231)
      | ~ v5_relat_1(k7_relat_1(B_229,A_230),A_231)
      | ~ v1_relat_1(k7_relat_1(B_229,A_230))
      | ~ v1_relat_1(B_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_20])).

tff(c_2180,plain,(
    ! [A_115] :
      ( r1_tarski(k9_relat_1('#skF_4',A_115),'#skF_2')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_115))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_688,c_2159])).

tff(c_2201,plain,(
    ! [A_115] : r1_tarski(k9_relat_1('#skF_4',A_115),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_692,c_2180])).

tff(c_495,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_502,plain,(
    ! [D_103] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_103) = k9_relat_1('#skF_4',D_103) ),
    inference(resolution,[status(thm)],[c_36,c_495])).

tff(c_34,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_503,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_34])).

tff(c_2209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2201,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:13:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.23  
% 5.02/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.02/2.24  
% 5.02/2.24  %Foreground sorts:
% 5.02/2.24  
% 5.02/2.24  
% 5.02/2.24  %Background operators:
% 5.02/2.24  
% 5.02/2.24  
% 5.02/2.24  %Foreground operators:
% 5.02/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.02/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/2.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.02/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/2.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.02/2.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.02/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.02/2.24  tff('#skF_2', type, '#skF_2': $i).
% 5.02/2.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.02/2.24  tff('#skF_3', type, '#skF_3': $i).
% 5.02/2.24  tff('#skF_1', type, '#skF_1': $i).
% 5.02/2.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.02/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.02/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.02/2.24  tff('#skF_4', type, '#skF_4': $i).
% 5.02/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/2.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.02/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.02/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/2.24  
% 5.02/2.26  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.02/2.26  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 5.02/2.26  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.02/2.26  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.02/2.26  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.02/2.26  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 5.02/2.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.02/2.26  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.02/2.26  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.02/2.26  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.02/2.26  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.02/2.26  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.02/2.26  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.02/2.26  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.02/2.26  tff(c_77, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.02/2.26  tff(c_83, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_77])).
% 5.02/2.26  tff(c_87, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_83])).
% 5.02/2.26  tff(c_45, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/2.26  tff(c_49, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_45])).
% 5.02/2.26  tff(c_50, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.02/2.26  tff(c_60, plain, (k2_xboole_0('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_49, c_50])).
% 5.02/2.26  tff(c_26, plain, (![B_20, A_19]: (r1_tarski(k7_relat_1(B_20, A_19), B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.02/2.26  tff(c_214, plain, (![B_59, A_60]: (k2_xboole_0(k7_relat_1(B_59, A_60), B_59)=B_59 | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_26, c_50])).
% 5.02/2.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.02/2.26  tff(c_103, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(k2_xboole_0(A_44, B_46), C_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.02/2.26  tff(c_112, plain, (![A_47, B_48]: (r1_tarski(A_47, k2_xboole_0(A_47, B_48)))), inference(resolution, [status(thm)], [c_6, c_103])).
% 5.02/2.26  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.02/2.26  tff(c_126, plain, (![A_3, B_4, B_48]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_48)))), inference(resolution, [status(thm)], [c_112, c_8])).
% 5.02/2.26  tff(c_641, plain, (![B_112, A_113, B_114]: (r1_tarski(k7_relat_1(B_112, A_113), k2_xboole_0(B_112, B_114)) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_214, c_126])).
% 5.02/2.26  tff(c_661, plain, (![A_113]: (r1_tarski(k7_relat_1('#skF_4', A_113), k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_641])).
% 5.02/2.26  tff(c_672, plain, (![A_115]: (r1_tarski(k7_relat_1('#skF_4', A_115), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_661])).
% 5.02/2.26  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/2.26  tff(c_84, plain, (![A_8, B_9]: (v1_relat_1(A_8) | ~v1_relat_1(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_77])).
% 5.02/2.26  tff(c_683, plain, (![A_115]: (v1_relat_1(k7_relat_1('#skF_4', A_115)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_672, c_84])).
% 5.02/2.26  tff(c_692, plain, (![A_115]: (v1_relat_1(k7_relat_1('#skF_4', A_115)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_683])).
% 5.02/2.26  tff(c_392, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.02/2.26  tff(c_400, plain, (![A_8, B_77, A_78]: (v5_relat_1(A_8, B_77) | ~r1_tarski(A_8, k2_zfmisc_1(A_78, B_77)))), inference(resolution, [status(thm)], [c_14, c_392])).
% 5.02/2.26  tff(c_688, plain, (![A_115]: (v5_relat_1(k7_relat_1('#skF_4', A_115), '#skF_2'))), inference(resolution, [status(thm)], [c_672, c_400])).
% 5.02/2.26  tff(c_340, plain, (![B_69, A_70]: (k2_relat_1(k7_relat_1(B_69, A_70))=k9_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.02/2.26  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.02/2.26  tff(c_2159, plain, (![B_229, A_230, A_231]: (r1_tarski(k9_relat_1(B_229, A_230), A_231) | ~v5_relat_1(k7_relat_1(B_229, A_230), A_231) | ~v1_relat_1(k7_relat_1(B_229, A_230)) | ~v1_relat_1(B_229))), inference(superposition, [status(thm), theory('equality')], [c_340, c_20])).
% 5.02/2.26  tff(c_2180, plain, (![A_115]: (r1_tarski(k9_relat_1('#skF_4', A_115), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', A_115)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_688, c_2159])).
% 5.02/2.26  tff(c_2201, plain, (![A_115]: (r1_tarski(k9_relat_1('#skF_4', A_115), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_692, c_2180])).
% 5.02/2.26  tff(c_495, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.02/2.26  tff(c_502, plain, (![D_103]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_103)=k9_relat_1('#skF_4', D_103))), inference(resolution, [status(thm)], [c_36, c_495])).
% 5.02/2.26  tff(c_34, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.02/2.26  tff(c_503, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_34])).
% 5.02/2.26  tff(c_2209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2201, c_503])).
% 5.02/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.26  
% 5.02/2.26  Inference rules
% 5.02/2.26  ----------------------
% 5.02/2.26  #Ref     : 0
% 5.02/2.26  #Sup     : 508
% 5.02/2.26  #Fact    : 0
% 5.02/2.26  #Define  : 0
% 5.02/2.26  #Split   : 2
% 5.02/2.26  #Chain   : 0
% 5.02/2.26  #Close   : 0
% 5.02/2.26  
% 5.02/2.26  Ordering : KBO
% 5.02/2.26  
% 5.02/2.26  Simplification rules
% 5.02/2.26  ----------------------
% 5.02/2.26  #Subsume      : 68
% 5.02/2.26  #Demod        : 194
% 5.02/2.26  #Tautology    : 174
% 5.02/2.26  #SimpNegUnit  : 0
% 5.02/2.26  #BackRed      : 2
% 5.02/2.26  
% 5.02/2.26  #Partial instantiations: 0
% 5.02/2.26  #Strategies tried      : 1
% 5.02/2.26  
% 5.02/2.26  Timing (in seconds)
% 5.02/2.26  ----------------------
% 5.02/2.26  Preprocessing        : 0.45
% 5.02/2.26  Parsing              : 0.23
% 5.02/2.26  CNF conversion       : 0.03
% 5.02/2.26  Main loop            : 0.91
% 5.02/2.26  Inferencing          : 0.32
% 5.02/2.26  Reduction            : 0.32
% 5.02/2.26  Demodulation         : 0.24
% 5.02/2.26  BG Simplification    : 0.04
% 5.02/2.26  Subsumption          : 0.18
% 5.02/2.26  Abstraction          : 0.05
% 5.02/2.27  MUC search           : 0.00
% 5.02/2.27  Cooper               : 0.00
% 5.02/2.27  Total                : 1.41
% 5.02/2.27  Index Insertion      : 0.00
% 5.02/2.27  Index Deletion       : 0.00
% 5.02/2.27  Index Matching       : 0.00
% 5.02/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
