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
% DateTime   : Thu Dec  3 10:05:26 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   66 (  74 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 135 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_89,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(k2_relat_1(B),k1_relat_1(C))
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(k5_relat_1(B,C),k9_relat_1(C,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_46,plain,(
    k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_12] : v1_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_24] : k2_funct_1(k6_relat_1(A_24)) = k6_relat_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_161,plain,(
    ! [B_50,A_51] :
      ( k10_relat_1(k2_funct_1(B_50),A_51) = k9_relat_1(B_50,A_51)
      | ~ v2_funct_1(B_50)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_170,plain,(
    ! [A_24,A_51] :
      ( k9_relat_1(k6_relat_1(A_24),A_51) = k10_relat_1(k6_relat_1(A_24),A_51)
      | ~ v2_funct_1(k6_relat_1(A_24))
      | ~ v1_funct_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_161])).

tff(c_174,plain,(
    ! [A_24,A_51] : k9_relat_1(k6_relat_1(A_24),A_51) = k10_relat_1(k6_relat_1(A_24),A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_34,c_170])).

tff(c_90,plain,(
    ! [C_36,A_37] :
      ( r2_hidden(C_36,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [C_36,A_37] :
      ( m1_subset_1(C_36,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(resolution,[status(thm)],[c_90,c_20])).

tff(c_134,plain,(
    ! [A_44,B_45] :
      ( k9_relat_1(k6_relat_1(A_44),B_45) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_138,plain,(
    ! [A_37,C_36] :
      ( k9_relat_1(k6_relat_1(A_37),C_36) = C_36
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(resolution,[status(thm)],[c_98,c_134])).

tff(c_185,plain,(
    ! [A_37,C_36] :
      ( k10_relat_1(k6_relat_1(A_37),C_36) = C_36
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_138])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_332,plain,(
    ! [B_75,A_76,C_77] :
      ( r1_tarski(k10_relat_1(B_75,A_76),k10_relat_1(k5_relat_1(B_75,C_77),k9_relat_1(C_77,A_76)))
      | ~ r1_tarski(k2_relat_1(B_75),k1_relat_1(C_77))
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_352,plain,(
    ! [A_11,A_76] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_11)),A_76),k10_relat_1(A_11,k9_relat_1(A_11,A_76)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_11))),k1_relat_1(A_11))
      | ~ v1_relat_1(A_11)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_332])).

tff(c_475,plain,(
    ! [A_84,A_85] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_84)),A_85),k10_relat_1(A_84,k9_relat_1(A_84,A_85)))
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_24,c_352])).

tff(c_489,plain,(
    ! [C_36,A_84] :
      ( r1_tarski(C_36,k10_relat_1(A_84,k9_relat_1(A_84,C_36)))
      | ~ v1_relat_1(A_84)
      | ~ r1_tarski(C_36,k1_relat_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_475])).

tff(c_211,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k10_relat_1(B_62,k9_relat_1(B_62,A_63)),A_63)
      | ~ v2_funct_1(B_62)
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_908,plain,(
    ! [B_119,A_120] :
      ( k10_relat_1(B_119,k9_relat_1(B_119,A_120)) = A_120
      | ~ r1_tarski(A_120,k10_relat_1(B_119,k9_relat_1(B_119,A_120)))
      | ~ v2_funct_1(B_119)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_211,c_2])).

tff(c_1085,plain,(
    ! [A_122,C_123] :
      ( k10_relat_1(A_122,k9_relat_1(A_122,C_123)) = C_123
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122)
      | ~ r1_tarski(C_123,k1_relat_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_489,c_908])).

tff(c_1113,plain,
    ( k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1085])).

tff(c_1129,plain,(
    k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1113])).

tff(c_1131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.60  
% 3.15/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.61  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.15/1.61  
% 3.15/1.61  %Foreground sorts:
% 3.15/1.61  
% 3.15/1.61  
% 3.15/1.61  %Background operators:
% 3.15/1.61  
% 3.15/1.61  
% 3.15/1.61  %Foreground operators:
% 3.15/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.15/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.15/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.15/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.15/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.15/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.61  
% 3.15/1.62  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.15/1.62  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.15/1.62  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.15/1.62  tff(f_89, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.15/1.62  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 3.15/1.62  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.15/1.62  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.15/1.62  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.15/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.62  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.15/1.62  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.15/1.62  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(C)) => r1_tarski(k10_relat_1(B, A), k10_relat_1(k5_relat_1(B, C), k9_relat_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_1)).
% 3.15/1.62  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 3.15/1.62  tff(c_46, plain, (k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.62  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.62  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.62  tff(c_48, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.62  tff(c_50, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.62  tff(c_32, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.62  tff(c_30, plain, (![A_12]: (v1_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.62  tff(c_34, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.62  tff(c_44, plain, (![A_24]: (k2_funct_1(k6_relat_1(A_24))=k6_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.62  tff(c_161, plain, (![B_50, A_51]: (k10_relat_1(k2_funct_1(B_50), A_51)=k9_relat_1(B_50, A_51) | ~v2_funct_1(B_50) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.62  tff(c_170, plain, (![A_24, A_51]: (k9_relat_1(k6_relat_1(A_24), A_51)=k10_relat_1(k6_relat_1(A_24), A_51) | ~v2_funct_1(k6_relat_1(A_24)) | ~v1_funct_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_161])).
% 3.15/1.62  tff(c_174, plain, (![A_24, A_51]: (k9_relat_1(k6_relat_1(A_24), A_51)=k10_relat_1(k6_relat_1(A_24), A_51))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_34, c_170])).
% 3.15/1.62  tff(c_90, plain, (![C_36, A_37]: (r2_hidden(C_36, k1_zfmisc_1(A_37)) | ~r1_tarski(C_36, A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.62  tff(c_20, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.62  tff(c_98, plain, (![C_36, A_37]: (m1_subset_1(C_36, k1_zfmisc_1(A_37)) | ~r1_tarski(C_36, A_37))), inference(resolution, [status(thm)], [c_90, c_20])).
% 3.15/1.62  tff(c_134, plain, (![A_44, B_45]: (k9_relat_1(k6_relat_1(A_44), B_45)=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.15/1.62  tff(c_138, plain, (![A_37, C_36]: (k9_relat_1(k6_relat_1(A_37), C_36)=C_36 | ~r1_tarski(C_36, A_37))), inference(resolution, [status(thm)], [c_98, c_134])).
% 3.15/1.62  tff(c_185, plain, (![A_37, C_36]: (k10_relat_1(k6_relat_1(A_37), C_36)=C_36 | ~r1_tarski(C_36, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_138])).
% 3.15/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.62  tff(c_24, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.62  tff(c_26, plain, (![A_11]: (k5_relat_1(k6_relat_1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.62  tff(c_332, plain, (![B_75, A_76, C_77]: (r1_tarski(k10_relat_1(B_75, A_76), k10_relat_1(k5_relat_1(B_75, C_77), k9_relat_1(C_77, A_76))) | ~r1_tarski(k2_relat_1(B_75), k1_relat_1(C_77)) | ~v1_relat_1(C_77) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.15/1.62  tff(c_352, plain, (![A_11, A_76]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_11)), A_76), k10_relat_1(A_11, k9_relat_1(A_11, A_76))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_11))), k1_relat_1(A_11)) | ~v1_relat_1(A_11) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_26, c_332])).
% 3.15/1.62  tff(c_475, plain, (![A_84, A_85]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_84)), A_85), k10_relat_1(A_84, k9_relat_1(A_84, A_85))) | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_24, c_352])).
% 3.15/1.62  tff(c_489, plain, (![C_36, A_84]: (r1_tarski(C_36, k10_relat_1(A_84, k9_relat_1(A_84, C_36))) | ~v1_relat_1(A_84) | ~r1_tarski(C_36, k1_relat_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_475])).
% 3.15/1.62  tff(c_211, plain, (![B_62, A_63]: (r1_tarski(k10_relat_1(B_62, k9_relat_1(B_62, A_63)), A_63) | ~v2_funct_1(B_62) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.62  tff(c_908, plain, (![B_119, A_120]: (k10_relat_1(B_119, k9_relat_1(B_119, A_120))=A_120 | ~r1_tarski(A_120, k10_relat_1(B_119, k9_relat_1(B_119, A_120))) | ~v2_funct_1(B_119) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_211, c_2])).
% 3.15/1.62  tff(c_1085, plain, (![A_122, C_123]: (k10_relat_1(A_122, k9_relat_1(A_122, C_123))=C_123 | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122) | ~r1_tarski(C_123, k1_relat_1(A_122)))), inference(resolution, [status(thm)], [c_489, c_908])).
% 3.15/1.62  tff(c_1113, plain, (k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3'))='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1085])).
% 3.15/1.62  tff(c_1129, plain, (k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_1113])).
% 3.15/1.62  tff(c_1131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1129])).
% 3.15/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.62  
% 3.15/1.62  Inference rules
% 3.15/1.62  ----------------------
% 3.15/1.62  #Ref     : 0
% 3.15/1.62  #Sup     : 237
% 3.15/1.62  #Fact    : 0
% 3.15/1.62  #Define  : 0
% 3.15/1.62  #Split   : 1
% 3.15/1.62  #Chain   : 0
% 3.15/1.62  #Close   : 0
% 3.15/1.62  
% 3.15/1.62  Ordering : KBO
% 3.15/1.62  
% 3.15/1.62  Simplification rules
% 3.15/1.62  ----------------------
% 3.15/1.62  #Subsume      : 35
% 3.15/1.62  #Demod        : 458
% 3.15/1.62  #Tautology    : 123
% 3.15/1.62  #SimpNegUnit  : 1
% 3.15/1.62  #BackRed      : 3
% 3.15/1.62  
% 3.15/1.62  #Partial instantiations: 0
% 3.15/1.62  #Strategies tried      : 1
% 3.15/1.62  
% 3.15/1.62  Timing (in seconds)
% 3.15/1.62  ----------------------
% 3.15/1.62  Preprocessing        : 0.34
% 3.15/1.62  Parsing              : 0.18
% 3.15/1.62  CNF conversion       : 0.03
% 3.15/1.62  Main loop            : 0.43
% 3.15/1.62  Inferencing          : 0.16
% 3.15/1.62  Reduction            : 0.15
% 3.15/1.62  Demodulation         : 0.11
% 3.15/1.62  BG Simplification    : 0.02
% 3.15/1.62  Subsumption          : 0.08
% 3.15/1.62  Abstraction          : 0.02
% 3.15/1.62  MUC search           : 0.00
% 3.15/1.62  Cooper               : 0.00
% 3.15/1.62  Total                : 0.80
% 3.15/1.62  Index Insertion      : 0.00
% 3.15/1.62  Index Deletion       : 0.00
% 3.15/1.62  Index Matching       : 0.00
% 3.15/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
