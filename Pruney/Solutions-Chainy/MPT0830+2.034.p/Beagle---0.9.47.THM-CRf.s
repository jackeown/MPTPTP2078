%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:30 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 127 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 214 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_53])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_75,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_91,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_54])).

tff(c_97,plain,(
    ! [A_49] :
      ( v1_relat_1(A_49)
      | ~ r1_tarski(A_49,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_91])).

tff(c_101,plain,(
    ! [A_16] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_16))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_104,plain,(
    ! [A_16] : v1_relat_1(k7_relat_1('#skF_4',A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_101])).

tff(c_135,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_144,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_194,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(k7_relat_1(C_78,A_79),A_79)
      | ~ v4_relat_1(C_78,B_80)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_204,plain,(
    ! [A_79] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_79),A_79)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_194])).

tff(c_211,plain,(
    ! [A_79] : v4_relat_1(k7_relat_1('#skF_4',A_79),A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_204])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    ! [A_45] :
      ( r1_tarski(A_45,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_300,plain,(
    ! [D_97,B_98,C_99,A_100] :
      ( m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(B_98,C_99)))
      | ~ r1_tarski(k1_relat_1(D_97),B_98)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_100,C_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_704,plain,(
    ! [A_147,B_148,C_149,A_150] :
      ( m1_subset_1(A_147,k1_zfmisc_1(k2_zfmisc_1(B_148,C_149)))
      | ~ r1_tarski(k1_relat_1(A_147),B_148)
      | ~ r1_tarski(A_147,k2_zfmisc_1(A_150,C_149)) ) ),
    inference(resolution,[status(thm)],[c_6,c_300])).

tff(c_842,plain,(
    ! [A_158,B_159] :
      ( m1_subset_1(A_158,k1_zfmisc_1(k2_zfmisc_1(B_159,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(A_158),B_159)
      | ~ r1_tarski(A_158,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_704])).

tff(c_222,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k5_relset_1(A_84,B_85,C_86,D_87) = k7_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_229,plain,(
    ! [D_87] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_87) = k7_relat_1('#skF_4',D_87) ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_231,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_32])).

tff(c_863,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_842,c_231])).

tff(c_1015,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_863])).

tff(c_1018,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1015])).

tff(c_1022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1018])).

tff(c_1023,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_1048,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_1023])).

tff(c_1052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_211,c_1048])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.50  
% 3.09/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.50  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.09/1.50  
% 3.09/1.50  %Foreground sorts:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Background operators:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Foreground operators:
% 3.09/1.50  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.09/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.09/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.50  
% 3.09/1.52  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.09/1.52  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 3.09/1.52  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.09/1.52  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.09/1.52  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.09/1.52  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.09/1.52  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.52  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 3.09/1.52  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.09/1.52  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.09/1.52  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.09/1.52  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.52  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.09/1.52  tff(c_47, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.52  tff(c_53, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_47])).
% 3.09/1.52  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_53])).
% 3.09/1.52  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.52  tff(c_36, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.52  tff(c_40, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_36])).
% 3.09/1.52  tff(c_75, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.52  tff(c_82, plain, (![A_48]: (r1_tarski(A_48, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.09/1.52  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.52  tff(c_54, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_47])).
% 3.09/1.52  tff(c_91, plain, (![A_48]: (v1_relat_1(A_48) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_54])).
% 3.09/1.52  tff(c_97, plain, (![A_49]: (v1_relat_1(A_49) | ~r1_tarski(A_49, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_91])).
% 3.09/1.52  tff(c_101, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_4', A_16)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_97])).
% 3.09/1.52  tff(c_104, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_4', A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_101])).
% 3.09/1.52  tff(c_135, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.52  tff(c_144, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_135])).
% 3.09/1.52  tff(c_194, plain, (![C_78, A_79, B_80]: (v4_relat_1(k7_relat_1(C_78, A_79), A_79) | ~v4_relat_1(C_78, B_80) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_204, plain, (![A_79]: (v4_relat_1(k7_relat_1('#skF_4', A_79), A_79) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_144, c_194])).
% 3.09/1.52  tff(c_211, plain, (![A_79]: (v4_relat_1(k7_relat_1('#skF_4', A_79), A_79))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_204])).
% 3.09/1.52  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.52  tff(c_81, plain, (![A_45]: (r1_tarski(A_45, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_45, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_75])).
% 3.09/1.52  tff(c_300, plain, (![D_97, B_98, C_99, A_100]: (m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(B_98, C_99))) | ~r1_tarski(k1_relat_1(D_97), B_98) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_100, C_99))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.52  tff(c_704, plain, (![A_147, B_148, C_149, A_150]: (m1_subset_1(A_147, k1_zfmisc_1(k2_zfmisc_1(B_148, C_149))) | ~r1_tarski(k1_relat_1(A_147), B_148) | ~r1_tarski(A_147, k2_zfmisc_1(A_150, C_149)))), inference(resolution, [status(thm)], [c_6, c_300])).
% 3.09/1.52  tff(c_842, plain, (![A_158, B_159]: (m1_subset_1(A_158, k1_zfmisc_1(k2_zfmisc_1(B_159, '#skF_3'))) | ~r1_tarski(k1_relat_1(A_158), B_159) | ~r1_tarski(A_158, '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_704])).
% 3.09/1.52  tff(c_222, plain, (![A_84, B_85, C_86, D_87]: (k5_relset_1(A_84, B_85, C_86, D_87)=k7_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.09/1.52  tff(c_229, plain, (![D_87]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_87)=k7_relat_1('#skF_4', D_87))), inference(resolution, [status(thm)], [c_34, c_222])).
% 3.09/1.52  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.09/1.52  tff(c_231, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_32])).
% 3.09/1.52  tff(c_863, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_842, c_231])).
% 3.09/1.52  tff(c_1015, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_863])).
% 3.09/1.52  tff(c_1018, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1015])).
% 3.09/1.52  tff(c_1022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_1018])).
% 3.09/1.52  tff(c_1023, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_863])).
% 3.09/1.52  tff(c_1048, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1023])).
% 3.09/1.52  tff(c_1052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_211, c_1048])).
% 3.09/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  Inference rules
% 3.09/1.52  ----------------------
% 3.09/1.52  #Ref     : 0
% 3.09/1.52  #Sup     : 216
% 3.09/1.52  #Fact    : 0
% 3.09/1.52  #Define  : 0
% 3.09/1.52  #Split   : 4
% 3.09/1.52  #Chain   : 0
% 3.09/1.52  #Close   : 0
% 3.09/1.52  
% 3.09/1.52  Ordering : KBO
% 3.09/1.52  
% 3.09/1.52  Simplification rules
% 3.09/1.52  ----------------------
% 3.09/1.52  #Subsume      : 31
% 3.09/1.52  #Demod        : 82
% 3.09/1.52  #Tautology    : 27
% 3.09/1.52  #SimpNegUnit  : 0
% 3.09/1.52  #BackRed      : 2
% 3.09/1.52  
% 3.09/1.52  #Partial instantiations: 0
% 3.09/1.52  #Strategies tried      : 1
% 3.09/1.52  
% 3.09/1.52  Timing (in seconds)
% 3.09/1.52  ----------------------
% 3.09/1.52  Preprocessing        : 0.31
% 3.09/1.52  Parsing              : 0.17
% 3.09/1.52  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.43
% 3.09/1.52  Inferencing          : 0.16
% 3.09/1.52  Reduction            : 0.13
% 3.09/1.52  Demodulation         : 0.09
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.52  Subsumption          : 0.09
% 3.09/1.52  Abstraction          : 0.02
% 3.09/1.52  MUC search           : 0.00
% 3.09/1.52  Cooper               : 0.00
% 3.09/1.52  Total                : 0.78
% 3.09/1.52  Index Insertion      : 0.00
% 3.09/1.52  Index Deletion       : 0.00
% 3.09/1.52  Index Matching       : 0.00
% 3.09/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
