%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 217 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 544 expanded)
%              Number of equality atoms :   42 ( 164 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [C_69,A_70,B_71] :
      ( m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ r1_tarski(k2_relat_1(C_69),B_71)
      | ~ r1_tarski(k1_relat_1(C_69),A_70)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [C_28,A_29,B_30] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r1_tarski(k2_relat_1(C_28),B_30)
      | ~ r1_tarski(k1_relat_1(C_28),A_29)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_4,B_5,C_6] :
      ( k1_relset_1(A_4,B_5,C_6) = k1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ r1_tarski(k2_relat_1(C_33),B_32)
      | ~ r1_tarski(k1_relat_1(C_33),A_31)
      | ~ v1_relat_1(C_33) ) ),
    inference(resolution,[status(thm)],[c_62,c_12])).

tff(c_92,plain,(
    ! [A_34,C_35] :
      ( k1_relset_1(A_34,k2_relat_1(C_35),C_35) = k1_relat_1(C_35)
      | ~ r1_tarski(k1_relat_1(C_35),A_34)
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_96,plain,(
    ! [C_35] :
      ( k1_relset_1(k1_relat_1(C_35),k2_relat_1(C_35),C_35) = k1_relat_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_44,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) = k1_xboole_0
      | k2_relat_1(A_16) != k1_xboole_0
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_54,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ r1_tarski(k2_relat_1(C_9),B_8)
      | ~ r1_tarski(k1_relat_1(C_9),A_7)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [B_36,C_37,A_38] :
      ( k1_xboole_0 = B_36
      | v1_funct_2(C_37,A_38,B_36)
      | k1_relset_1(A_38,B_36,C_37) != A_38
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_142,plain,(
    ! [B_54,C_55,A_56] :
      ( k1_xboole_0 = B_54
      | v1_funct_2(C_55,A_56,B_54)
      | k1_relset_1(A_56,B_54,C_55) != A_56
      | ~ r1_tarski(k2_relat_1(C_55),B_54)
      | ~ r1_tarski(k1_relat_1(C_55),A_56)
      | ~ v1_relat_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_14,c_97])).

tff(c_147,plain,(
    ! [C_57,A_58] :
      ( k2_relat_1(C_57) = k1_xboole_0
      | v1_funct_2(C_57,A_58,k2_relat_1(C_57))
      | k1_relset_1(A_58,k2_relat_1(C_57),C_57) != A_58
      | ~ r1_tarski(k1_relat_1(C_57),A_58)
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_56,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_156,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_147,c_56])).

tff(c_163,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_156])).

tff(c_164,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_163])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_172,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_201,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_179,c_172])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_6,c_201])).

tff(c_211,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_212,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_406,plain,(
    ! [C_114,A_115,B_116] :
      ( m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ r1_tarski(k2_relat_1(C_114),B_116)
      | ~ r1_tarski(k1_relat_1(C_114),A_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_230,plain,(
    ! [C_82,A_83,B_84] :
      ( m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_255,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ r1_tarski(k2_relat_1(C_87),B_86)
      | ~ r1_tarski(k1_relat_1(C_87),A_85)
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_230,c_12])).

tff(c_257,plain,(
    ! [A_85,B_86] :
      ( k1_relset_1(A_85,B_86,'#skF_1') = k1_relat_1('#skF_1')
      | ~ r1_tarski(k1_xboole_0,B_86)
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_85)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_255])).

tff(c_264,plain,(
    ! [A_88,B_89] :
      ( k1_relset_1(A_88,B_89,'#skF_1') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_89)
      | ~ r1_tarski(k1_xboole_0,A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_211,c_211,c_257])).

tff(c_269,plain,(
    ! [A_90] :
      ( k1_relset_1(A_90,k1_xboole_0,'#skF_1') = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_274,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_20,plain,(
    ! [C_12,B_11] :
      ( v1_funct_2(C_12,k1_xboole_0,B_11)
      | k1_relset_1(k1_xboole_0,B_11,C_12) != k1_xboole_0
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_364,plain,(
    ! [C_107,B_108] :
      ( v1_funct_2(C_107,k1_xboole_0,B_108)
      | k1_relset_1(k1_xboole_0,B_108,C_107) != k1_xboole_0
      | ~ r1_tarski(k2_relat_1(C_107),B_108)
      | ~ r1_tarski(k1_relat_1(C_107),k1_xboole_0)
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_230,c_20])).

tff(c_367,plain,(
    ! [B_108] :
      ( v1_funct_2('#skF_1',k1_xboole_0,B_108)
      | k1_relset_1(k1_xboole_0,B_108,'#skF_1') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_108)
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_xboole_0)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_364])).

tff(c_375,plain,(
    ! [B_109] :
      ( v1_funct_2('#skF_1',k1_xboole_0,B_109)
      | k1_relset_1(k1_xboole_0,B_109,'#skF_1') != k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_211,c_367])).

tff(c_226,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_211,c_212,c_211,c_34])).

tff(c_227,plain,(
    ~ v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_389,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_375,c_227])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_274,c_389])).

tff(c_402,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_417,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_406,c_402])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6,c_211,c_6,c_212,c_417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.32  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.59/1.32  
% 2.59/1.32  %Foreground sorts:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Background operators:
% 2.59/1.32  
% 2.59/1.32  
% 2.59/1.32  %Foreground operators:
% 2.59/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.59/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.59/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.32  
% 2.59/1.34  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.59/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.34  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.59/1.34  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.59/1.34  tff(f_37, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.59/1.34  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.59/1.34  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.34  tff(c_179, plain, (![C_69, A_70, B_71]: (m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~r1_tarski(k2_relat_1(C_69), B_71) | ~r1_tarski(k1_relat_1(C_69), A_70) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.34  tff(c_62, plain, (![C_28, A_29, B_30]: (m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r1_tarski(k2_relat_1(C_28), B_30) | ~r1_tarski(k1_relat_1(C_28), A_29) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.34  tff(c_12, plain, (![A_4, B_5, C_6]: (k1_relset_1(A_4, B_5, C_6)=k1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.34  tff(c_87, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~r1_tarski(k2_relat_1(C_33), B_32) | ~r1_tarski(k1_relat_1(C_33), A_31) | ~v1_relat_1(C_33))), inference(resolution, [status(thm)], [c_62, c_12])).
% 2.59/1.34  tff(c_92, plain, (![A_34, C_35]: (k1_relset_1(A_34, k2_relat_1(C_35), C_35)=k1_relat_1(C_35) | ~r1_tarski(k1_relat_1(C_35), A_34) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.59/1.34  tff(c_96, plain, (![C_35]: (k1_relset_1(k1_relat_1(C_35), k2_relat_1(C_35), C_35)=k1_relat_1(C_35) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_6, c_92])).
% 2.59/1.34  tff(c_44, plain, (![A_16]: (k1_relat_1(A_16)=k1_xboole_0 | k2_relat_1(A_16)!=k1_xboole_0 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.34  tff(c_48, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | k2_relat_1('#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_44])).
% 2.59/1.34  tff(c_54, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.59/1.34  tff(c_14, plain, (![C_9, A_7, B_8]: (m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~r1_tarski(k2_relat_1(C_9), B_8) | ~r1_tarski(k1_relat_1(C_9), A_7) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.34  tff(c_97, plain, (![B_36, C_37, A_38]: (k1_xboole_0=B_36 | v1_funct_2(C_37, A_38, B_36) | k1_relset_1(A_38, B_36, C_37)!=A_38 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_36))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.34  tff(c_142, plain, (![B_54, C_55, A_56]: (k1_xboole_0=B_54 | v1_funct_2(C_55, A_56, B_54) | k1_relset_1(A_56, B_54, C_55)!=A_56 | ~r1_tarski(k2_relat_1(C_55), B_54) | ~r1_tarski(k1_relat_1(C_55), A_56) | ~v1_relat_1(C_55))), inference(resolution, [status(thm)], [c_14, c_97])).
% 2.59/1.34  tff(c_147, plain, (![C_57, A_58]: (k2_relat_1(C_57)=k1_xboole_0 | v1_funct_2(C_57, A_58, k2_relat_1(C_57)) | k1_relset_1(A_58, k2_relat_1(C_57), C_57)!=A_58 | ~r1_tarski(k1_relat_1(C_57), A_58) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_6, c_142])).
% 2.59/1.34  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.34  tff(c_28, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.34  tff(c_34, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 2.59/1.34  tff(c_56, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.59/1.34  tff(c_156, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_147, c_56])).
% 2.59/1.34  tff(c_163, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_156])).
% 2.59/1.34  tff(c_164, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_163])).
% 2.59/1.34  tff(c_167, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_164])).
% 2.59/1.34  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 2.59/1.34  tff(c_172, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_34])).
% 2.59/1.34  tff(c_201, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_179, c_172])).
% 2.59/1.34  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_6, c_201])).
% 2.59/1.34  tff(c_211, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.59/1.34  tff(c_212, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.59/1.34  tff(c_406, plain, (![C_114, A_115, B_116]: (m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~r1_tarski(k2_relat_1(C_114), B_116) | ~r1_tarski(k1_relat_1(C_114), A_115) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.34  tff(c_230, plain, (![C_82, A_83, B_84]: (m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.34  tff(c_255, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~r1_tarski(k2_relat_1(C_87), B_86) | ~r1_tarski(k1_relat_1(C_87), A_85) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_230, c_12])).
% 2.59/1.34  tff(c_257, plain, (![A_85, B_86]: (k1_relset_1(A_85, B_86, '#skF_1')=k1_relat_1('#skF_1') | ~r1_tarski(k1_xboole_0, B_86) | ~r1_tarski(k1_relat_1('#skF_1'), A_85) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_255])).
% 2.59/1.34  tff(c_264, plain, (![A_88, B_89]: (k1_relset_1(A_88, B_89, '#skF_1')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_89) | ~r1_tarski(k1_xboole_0, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_211, c_211, c_257])).
% 2.59/1.34  tff(c_269, plain, (![A_90]: (k1_relset_1(A_90, k1_xboole_0, '#skF_1')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_90))), inference(resolution, [status(thm)], [c_6, c_264])).
% 2.59/1.34  tff(c_274, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_269])).
% 2.59/1.34  tff(c_20, plain, (![C_12, B_11]: (v1_funct_2(C_12, k1_xboole_0, B_11) | k1_relset_1(k1_xboole_0, B_11, C_12)!=k1_xboole_0 | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_11))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.34  tff(c_364, plain, (![C_107, B_108]: (v1_funct_2(C_107, k1_xboole_0, B_108) | k1_relset_1(k1_xboole_0, B_108, C_107)!=k1_xboole_0 | ~r1_tarski(k2_relat_1(C_107), B_108) | ~r1_tarski(k1_relat_1(C_107), k1_xboole_0) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_230, c_20])).
% 2.59/1.34  tff(c_367, plain, (![B_108]: (v1_funct_2('#skF_1', k1_xboole_0, B_108) | k1_relset_1(k1_xboole_0, B_108, '#skF_1')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_108) | ~r1_tarski(k1_relat_1('#skF_1'), k1_xboole_0) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_364])).
% 2.59/1.34  tff(c_375, plain, (![B_109]: (v1_funct_2('#skF_1', k1_xboole_0, B_109) | k1_relset_1(k1_xboole_0, B_109, '#skF_1')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_211, c_367])).
% 2.59/1.34  tff(c_226, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_211, c_212, c_211, c_34])).
% 2.59/1.34  tff(c_227, plain, (~v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_226])).
% 2.59/1.34  tff(c_389, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')!=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_375, c_227])).
% 2.59/1.34  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_274, c_389])).
% 2.59/1.34  tff(c_402, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(splitRight, [status(thm)], [c_226])).
% 2.59/1.34  tff(c_417, plain, (~r1_tarski(k2_relat_1('#skF_1'), k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_1'), k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_406, c_402])).
% 2.59/1.34  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_6, c_211, c_6, c_212, c_417])).
% 2.59/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.34  
% 2.59/1.34  Inference rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Ref     : 0
% 2.59/1.34  #Sup     : 68
% 2.59/1.34  #Fact    : 0
% 2.59/1.34  #Define  : 0
% 2.59/1.34  #Split   : 6
% 2.59/1.34  #Chain   : 0
% 2.59/1.34  #Close   : 0
% 2.59/1.34  
% 2.59/1.34  Ordering : KBO
% 2.59/1.34  
% 2.59/1.34  Simplification rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Subsume      : 2
% 2.59/1.34  #Demod        : 105
% 2.59/1.34  #Tautology    : 22
% 2.59/1.34  #SimpNegUnit  : 2
% 2.59/1.34  #BackRed      : 16
% 2.59/1.34  
% 2.59/1.34  #Partial instantiations: 0
% 2.59/1.34  #Strategies tried      : 1
% 2.59/1.34  
% 2.59/1.34  Timing (in seconds)
% 2.59/1.34  ----------------------
% 2.59/1.34  Preprocessing        : 0.30
% 2.59/1.34  Parsing              : 0.16
% 2.59/1.34  CNF conversion       : 0.02
% 2.59/1.34  Main loop            : 0.27
% 2.59/1.34  Inferencing          : 0.10
% 2.59/1.34  Reduction            : 0.07
% 2.59/1.34  Demodulation         : 0.05
% 2.59/1.34  BG Simplification    : 0.02
% 2.59/1.34  Subsumption          : 0.06
% 2.59/1.34  Abstraction          : 0.01
% 2.59/1.34  MUC search           : 0.00
% 2.59/1.34  Cooper               : 0.00
% 2.59/1.34  Total                : 0.60
% 2.59/1.34  Index Insertion      : 0.00
% 2.59/1.34  Index Deletion       : 0.00
% 2.59/1.34  Index Matching       : 0.00
% 2.59/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
