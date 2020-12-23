%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:51 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 167 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_199,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_214,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_51,c_199])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(A_6)
      | ~ v1_relat_1(B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_231,plain,(
    ! [A_75] :
      ( v1_relat_1(A_75)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_214,c_60])).

tff(c_240,plain,(
    ! [A_76] :
      ( v1_relat_1(A_76)
      | ~ r1_tarski(A_76,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_231])).

tff(c_248,plain,(
    ! [A_17] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_17))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_256,plain,(
    ! [A_17] : v1_relat_1(k7_relat_1('#skF_4',A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_248])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_339,plain,(
    ! [A_98,A_99] :
      ( r1_tarski(A_98,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_98,A_99)
      | ~ r1_tarski(A_99,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_214,c_8])).

tff(c_442,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(k7_relat_1(B_116,A_117),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_116,'#skF_4')
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_24,c_339])).

tff(c_101,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_109,plain,(
    ! [A_6,B_46,A_47] :
      ( v5_relat_1(A_6,B_46)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_47,B_46)) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_461,plain,(
    ! [B_116,A_117] :
      ( v5_relat_1(k7_relat_1(B_116,A_117),'#skF_2')
      | ~ r1_tarski(B_116,'#skF_4')
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_442,c_109])).

tff(c_137,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(k7_relat_1(B_56,A_57)) = k9_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_693,plain,(
    ! [B_152,A_153,A_154] :
      ( r1_tarski(k9_relat_1(B_152,A_153),A_154)
      | ~ v5_relat_1(k7_relat_1(B_152,A_153),A_154)
      | ~ v1_relat_1(k7_relat_1(B_152,A_153))
      | ~ v1_relat_1(B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_18])).

tff(c_1175,plain,(
    ! [B_214,A_215] :
      ( r1_tarski(k9_relat_1(B_214,A_215),'#skF_2')
      | ~ v1_relat_1(k7_relat_1(B_214,A_215))
      | ~ r1_tarski(B_214,'#skF_4')
      | ~ v1_relat_1(B_214) ) ),
    inference(resolution,[status(thm)],[c_461,c_693])).

tff(c_260,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_267,plain,(
    ! [D_81] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_81) = k9_relat_1('#skF_4',D_81) ),
    inference(resolution,[status(thm)],[c_34,c_260])).

tff(c_32,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_270,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_32])).

tff(c_1180,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1175,c_270])).

tff(c_1192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6,c_256,c_1180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.68  
% 3.31/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.31/1.69  
% 3.31/1.69  %Foreground sorts:
% 3.31/1.69  
% 3.31/1.69  
% 3.31/1.69  %Background operators:
% 3.31/1.69  
% 3.31/1.69  
% 3.31/1.69  %Foreground operators:
% 3.31/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.31/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.69  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.31/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.31/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.31/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.56/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.69  
% 3.56/1.70  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.56/1.70  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_2)).
% 3.56/1.70  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.56/1.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.70  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.56/1.70  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.70  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.56/1.70  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.70  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.56/1.70  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.56/1.70  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.56/1.70  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.70  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.56/1.70  tff(c_53, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.56/1.70  tff(c_59, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_53])).
% 3.56/1.70  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 3.56/1.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.70  tff(c_24, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.70  tff(c_43, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.70  tff(c_51, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_43])).
% 3.56/1.70  tff(c_199, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.70  tff(c_214, plain, (![A_75]: (r1_tarski(A_75, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_51, c_199])).
% 3.56/1.70  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.70  tff(c_60, plain, (![A_6, B_7]: (v1_relat_1(A_6) | ~v1_relat_1(B_7) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_53])).
% 3.56/1.70  tff(c_231, plain, (![A_75]: (v1_relat_1(A_75) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_214, c_60])).
% 3.56/1.70  tff(c_240, plain, (![A_76]: (v1_relat_1(A_76) | ~r1_tarski(A_76, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_231])).
% 3.56/1.70  tff(c_248, plain, (![A_17]: (v1_relat_1(k7_relat_1('#skF_4', A_17)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_240])).
% 3.56/1.70  tff(c_256, plain, (![A_17]: (v1_relat_1(k7_relat_1('#skF_4', A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_248])).
% 3.56/1.70  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.70  tff(c_339, plain, (![A_98, A_99]: (r1_tarski(A_98, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_98, A_99) | ~r1_tarski(A_99, '#skF_4'))), inference(resolution, [status(thm)], [c_214, c_8])).
% 3.56/1.70  tff(c_442, plain, (![B_116, A_117]: (r1_tarski(k7_relat_1(B_116, A_117), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(B_116, '#skF_4') | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_24, c_339])).
% 3.56/1.70  tff(c_101, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.56/1.70  tff(c_109, plain, (![A_6, B_46, A_47]: (v5_relat_1(A_6, B_46) | ~r1_tarski(A_6, k2_zfmisc_1(A_47, B_46)))), inference(resolution, [status(thm)], [c_12, c_101])).
% 3.56/1.70  tff(c_461, plain, (![B_116, A_117]: (v5_relat_1(k7_relat_1(B_116, A_117), '#skF_2') | ~r1_tarski(B_116, '#skF_4') | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_442, c_109])).
% 3.56/1.70  tff(c_137, plain, (![B_56, A_57]: (k2_relat_1(k7_relat_1(B_56, A_57))=k9_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.70  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.70  tff(c_693, plain, (![B_152, A_153, A_154]: (r1_tarski(k9_relat_1(B_152, A_153), A_154) | ~v5_relat_1(k7_relat_1(B_152, A_153), A_154) | ~v1_relat_1(k7_relat_1(B_152, A_153)) | ~v1_relat_1(B_152))), inference(superposition, [status(thm), theory('equality')], [c_137, c_18])).
% 3.56/1.70  tff(c_1175, plain, (![B_214, A_215]: (r1_tarski(k9_relat_1(B_214, A_215), '#skF_2') | ~v1_relat_1(k7_relat_1(B_214, A_215)) | ~r1_tarski(B_214, '#skF_4') | ~v1_relat_1(B_214))), inference(resolution, [status(thm)], [c_461, c_693])).
% 3.56/1.70  tff(c_260, plain, (![A_78, B_79, C_80, D_81]: (k7_relset_1(A_78, B_79, C_80, D_81)=k9_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.70  tff(c_267, plain, (![D_81]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_81)=k9_relat_1('#skF_4', D_81))), inference(resolution, [status(thm)], [c_34, c_260])).
% 3.56/1.70  tff(c_32, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.56/1.70  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_32])).
% 3.56/1.70  tff(c_1180, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1175, c_270])).
% 3.56/1.70  tff(c_1192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_6, c_256, c_1180])).
% 3.56/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.70  
% 3.56/1.70  Inference rules
% 3.56/1.70  ----------------------
% 3.56/1.70  #Ref     : 0
% 3.56/1.70  #Sup     : 246
% 3.56/1.70  #Fact    : 0
% 3.56/1.70  #Define  : 0
% 3.56/1.70  #Split   : 3
% 3.56/1.70  #Chain   : 0
% 3.56/1.70  #Close   : 0
% 3.56/1.70  
% 3.56/1.70  Ordering : KBO
% 3.56/1.70  
% 3.56/1.70  Simplification rules
% 3.56/1.70  ----------------------
% 3.56/1.70  #Subsume      : 43
% 3.56/1.70  #Demod        : 69
% 3.56/1.70  #Tautology    : 29
% 3.56/1.70  #SimpNegUnit  : 0
% 3.56/1.70  #BackRed      : 1
% 3.56/1.70  
% 3.56/1.70  #Partial instantiations: 0
% 3.56/1.70  #Strategies tried      : 1
% 3.56/1.70  
% 3.56/1.70  Timing (in seconds)
% 3.56/1.70  ----------------------
% 3.56/1.70  Preprocessing        : 0.38
% 3.56/1.70  Parsing              : 0.19
% 3.56/1.70  CNF conversion       : 0.02
% 3.56/1.70  Main loop            : 0.47
% 3.56/1.70  Inferencing          : 0.17
% 3.56/1.70  Reduction            : 0.14
% 3.56/1.70  Demodulation         : 0.10
% 3.56/1.70  BG Simplification    : 0.02
% 3.56/1.70  Subsumption          : 0.10
% 3.56/1.71  Abstraction          : 0.03
% 3.56/1.71  MUC search           : 0.00
% 3.56/1.71  Cooper               : 0.00
% 3.56/1.71  Total                : 0.88
% 3.56/1.71  Index Insertion      : 0.00
% 3.56/1.71  Index Deletion       : 0.00
% 3.56/1.71  Index Matching       : 0.00
% 3.56/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
