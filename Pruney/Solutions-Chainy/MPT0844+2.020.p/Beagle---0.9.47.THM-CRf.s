%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   34 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 (  83 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_291,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k5_relset_1(A_98,B_99,C_100,D_101) = k7_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_298,plain,(
    ! [D_101] : k5_relset_1('#skF_5','#skF_3','#skF_6',D_101) = k7_relat_1('#skF_6',D_101) ),
    inference(resolution,[status(thm)],[c_34,c_291])).

tff(c_30,plain,(
    k5_relset_1('#skF_5','#skF_3','#skF_6','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_299,plain,(
    k7_relat_1('#skF_6','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_30])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_35,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_63,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_242,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( ~ r1_xboole_0(A_82,B_83)
      | r1_xboole_0(k2_zfmisc_1(A_82,C_84),k2_zfmisc_1(B_83,D_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_xboole_0(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_565,plain,(
    ! [C_140,A_143,A_142,B_141,D_139] :
      ( r1_xboole_0(A_142,k2_zfmisc_1(B_141,D_139))
      | ~ r1_tarski(A_142,k2_zfmisc_1(A_143,C_140))
      | ~ r1_xboole_0(A_143,B_141) ) ),
    inference(resolution,[status(thm)],[c_242,c_10])).

tff(c_569,plain,(
    ! [B_144,D_145] :
      ( r1_xboole_0('#skF_6',k2_zfmisc_1(B_144,D_145))
      | ~ r1_xboole_0('#skF_5',B_144) ) ),
    inference(resolution,[status(thm)],[c_71,c_565])).

tff(c_276,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,k2_zfmisc_1(A_97,k2_relat_1(B_96))) = k7_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_285,plain,(
    ! [B_96,A_97,C_7] :
      ( ~ r1_xboole_0(B_96,k2_zfmisc_1(A_97,k2_relat_1(B_96)))
      | ~ r2_hidden(C_7,k7_relat_1(B_96,A_97))
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_6])).

tff(c_572,plain,(
    ! [C_7,B_144] :
      ( ~ r2_hidden(C_7,k7_relat_1('#skF_6',B_144))
      | ~ v1_relat_1('#skF_6')
      | ~ r1_xboole_0('#skF_5',B_144) ) ),
    inference(resolution,[status(thm)],[c_569,c_285])).

tff(c_586,plain,(
    ! [C_146,B_147] :
      ( ~ r2_hidden(C_146,k7_relat_1('#skF_6',B_147))
      | ~ r1_xboole_0('#skF_5',B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_572])).

tff(c_592,plain,(
    ! [B_148] :
      ( ~ r1_xboole_0('#skF_5',B_148)
      | k7_relat_1('#skF_6',B_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_586])).

tff(c_614,plain,(
    k7_relat_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_592])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.42  
% 2.57/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.57/1.42  
% 2.57/1.42  %Foreground sorts:
% 2.57/1.42  
% 2.57/1.42  
% 2.57/1.42  %Background operators:
% 2.57/1.42  
% 2.57/1.42  
% 2.57/1.42  %Foreground operators:
% 2.57/1.42  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.57/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.57/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.57/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.42  
% 2.57/1.43  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.57/1.43  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.57/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.57/1.43  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.57/1.43  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.57/1.43  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.57/1.43  tff(f_65, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.57/1.43  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.57/1.43  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 2.57/1.43  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.57/1.43  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.43  tff(c_291, plain, (![A_98, B_99, C_100, D_101]: (k5_relset_1(A_98, B_99, C_100, D_101)=k7_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.57/1.43  tff(c_298, plain, (![D_101]: (k5_relset_1('#skF_5', '#skF_3', '#skF_6', D_101)=k7_relat_1('#skF_6', D_101))), inference(resolution, [status(thm)], [c_34, c_291])).
% 2.57/1.43  tff(c_30, plain, (k5_relset_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.43  tff(c_299, plain, (k7_relat_1('#skF_6', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_298, c_30])).
% 2.57/1.43  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.57/1.43  tff(c_35, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.43  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_35])).
% 2.57/1.43  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.43  tff(c_103, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.57/1.43  tff(c_112, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_103])).
% 2.57/1.43  tff(c_63, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.43  tff(c_71, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.57/1.43  tff(c_242, plain, (![A_82, B_83, C_84, D_85]: (~r1_xboole_0(A_82, B_83) | r1_xboole_0(k2_zfmisc_1(A_82, C_84), k2_zfmisc_1(B_83, D_85)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.43  tff(c_10, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_xboole_0(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.43  tff(c_565, plain, (![C_140, A_143, A_142, B_141, D_139]: (r1_xboole_0(A_142, k2_zfmisc_1(B_141, D_139)) | ~r1_tarski(A_142, k2_zfmisc_1(A_143, C_140)) | ~r1_xboole_0(A_143, B_141))), inference(resolution, [status(thm)], [c_242, c_10])).
% 2.57/1.43  tff(c_569, plain, (![B_144, D_145]: (r1_xboole_0('#skF_6', k2_zfmisc_1(B_144, D_145)) | ~r1_xboole_0('#skF_5', B_144))), inference(resolution, [status(thm)], [c_71, c_565])).
% 2.57/1.43  tff(c_276, plain, (![B_96, A_97]: (k3_xboole_0(B_96, k2_zfmisc_1(A_97, k2_relat_1(B_96)))=k7_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.43  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.43  tff(c_285, plain, (![B_96, A_97, C_7]: (~r1_xboole_0(B_96, k2_zfmisc_1(A_97, k2_relat_1(B_96))) | ~r2_hidden(C_7, k7_relat_1(B_96, A_97)) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_276, c_6])).
% 2.57/1.43  tff(c_572, plain, (![C_7, B_144]: (~r2_hidden(C_7, k7_relat_1('#skF_6', B_144)) | ~v1_relat_1('#skF_6') | ~r1_xboole_0('#skF_5', B_144))), inference(resolution, [status(thm)], [c_569, c_285])).
% 2.57/1.43  tff(c_586, plain, (![C_146, B_147]: (~r2_hidden(C_146, k7_relat_1('#skF_6', B_147)) | ~r1_xboole_0('#skF_5', B_147))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_572])).
% 2.57/1.43  tff(c_592, plain, (![B_148]: (~r1_xboole_0('#skF_5', B_148) | k7_relat_1('#skF_6', B_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_586])).
% 2.57/1.43  tff(c_614, plain, (k7_relat_1('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_592])).
% 2.57/1.43  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_299, c_614])).
% 2.57/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.43  
% 2.57/1.43  Inference rules
% 2.57/1.43  ----------------------
% 2.57/1.43  #Ref     : 0
% 2.57/1.43  #Sup     : 140
% 2.57/1.43  #Fact    : 0
% 2.57/1.43  #Define  : 0
% 2.57/1.43  #Split   : 5
% 2.57/1.43  #Chain   : 0
% 2.57/1.43  #Close   : 0
% 2.57/1.43  
% 2.57/1.43  Ordering : KBO
% 2.57/1.43  
% 2.57/1.44  Simplification rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Subsume      : 20
% 2.57/1.44  #Demod        : 11
% 2.57/1.44  #Tautology    : 41
% 2.57/1.44  #SimpNegUnit  : 9
% 2.57/1.44  #BackRed      : 1
% 2.57/1.44  
% 2.57/1.44  #Partial instantiations: 0
% 2.57/1.44  #Strategies tried      : 1
% 2.57/1.44  
% 2.57/1.44  Timing (in seconds)
% 2.57/1.44  ----------------------
% 2.57/1.44  Preprocessing        : 0.33
% 2.57/1.44  Parsing              : 0.18
% 2.57/1.44  CNF conversion       : 0.02
% 2.57/1.44  Main loop            : 0.32
% 2.57/1.44  Inferencing          : 0.13
% 2.57/1.44  Reduction            : 0.08
% 2.57/1.44  Demodulation         : 0.05
% 2.57/1.44  BG Simplification    : 0.02
% 2.57/1.44  Subsumption          : 0.07
% 2.57/1.44  Abstraction          : 0.02
% 2.57/1.44  MUC search           : 0.00
% 2.57/1.44  Cooper               : 0.00
% 2.57/1.44  Total                : 0.68
% 2.57/1.44  Index Insertion      : 0.00
% 2.57/1.44  Index Deletion       : 0.00
% 2.57/1.44  Index Matching       : 0.00
% 2.57/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
